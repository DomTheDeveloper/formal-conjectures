// Compact and slice a lean4export 3.1 proof. The output is checked by a separate Lean kernel.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>
#include <zstd.h>

using U = uint32_t;
using Bytes = std::vector<uint8_t>;
namespace fs = std::filesystem;
static void require(bool condition, std::string_view what) {
    if (!condition)
        throw std::runtime_error(std::string(what));
}
static U number(std::string_view s) {
    U n;
    auto [end, err] = std::from_chars(s.data(), s.data() + s.size(), n);
    require(err == std::errc() && end != s.data(), "missing or out-of-range numeric field");
    return n;
}
static size_t field_pos(std::string_view s, std::string_view key) {
    size_t p = s.find(key);
    if (p == s.npos)
        throw std::runtime_error("missing field " + std::string(key) + " in " +
                                 std::string(s.substr(0, 240)));
    return p + key.size();
}
static U field(std::string_view s, std::string_view key) {
    return number(s.substr(field_pos(s, key)));
}
enum Kind : uint8_t { Atom, Unary, Pair, Triple, Constant, Projection, Declaration };
struct Event {
    Kind kind;
    U a = 0, b = 0, c = 0;
};
static std::string_view first_key(std::string_view s) {
    require(s.starts_with("{\""), "bad JSON record");
    auto end = s.find('"', 2);
    return s.substr(2, end - 2);
}
static bool decl_key(std::string_view s) {
    return s == "axiom" || s == "thm" || s == "def" || s == "opaque" || s == "inductive" ||
           s == "quot";
}
static std::string_view expr_key(std::string_view s, std::string_view k) {
    if (k != "ie")
        return k;
    auto p = s.find(",\"");
    require(p != s.npos, "bad expression tag");
    p += 2;
    return s.substr(p, s.find('"', p) - p);
}
static Event expr_event(std::string_view s, std::string_view k) {
    if (k == "app")
        return {Pair, field(s, "\"arg\":"), field(s, "\"fn\":")};
    if (k == "forallE" || k == "lam")
        return {Pair, field(s, "\"body\":"), field(s, "\"type\":")};
    if (k == "letE")
        return {Triple, field(s, "\"body\":"), field(s, "\"type\":"), field(s, "\"value\":")};
    if (k == "const")
        return {Constant, field(s, "\"name\":")};
    if (k == "proj")
        return {Projection, field(s, "\"struct\":"), field(s, "\"typeName\":")};
    if (k == "mdata")
        return {Unary, field(s, "\"expr\":")};
    if (k == "bvar" || k == "sort" || k == "natVal" || k == "strVal")
        return {Atom};
    throw std::runtime_error("unrecognized expression: " + std::string(k));
}
static bool non_expr(std::string_view k) {
    return k == "meta" || k == "in" || k == "il" || k == "succ" || k == "max" || k == "imax" ||
           k == "param";
}
static void write_u(std::ostream &out, U x) {
    out.write(reinterpret_cast<const char *>(&x), 4);
}
static U read_u(std::istream &in) {
    U x;
    require(bool(in.read(reinterpret_cast<char *>(&x), 4)), "truncated uint32");
    return x;
}
static void put(Bytes &b, U x) {
    while (x >= 128) {
        b.push_back((x & 127) | 128);
        x >>= 7;
    }
    b.push_back(x);
}
static U get(const Bytes &b, size_t &pos) {
    U x = 0;
    for (unsigned n = 0; n <= 28; n += 7) {
        require(pos < b.size(), "truncated block");
        U v = b[pos++];
        x |= (v & 127) << n;
        if (v < 128)
            return x;
    }
    throw std::runtime_error("invalid varint");
}
static U ref_code(U pos, U child) {
    require(child < pos, "non-earlier expression reference");
    return child <= pos / 2 ? 2 * child : 2 * (pos - child) - 1;
}
static U ref_value(U pos, U x) {
    return x & 1 ? pos - (x / 2 + 1) : x / 2;
}
static void put_event(Bytes &raw, const Event &e, U pos) {
    raw.push_back(e.kind);
    switch (e.kind) {
    case Triple:
        put(raw, ref_code(pos, e.c));
        [[fallthrough]];
    case Pair:
        put(raw, ref_code(pos, e.b));
        [[fallthrough]];
    case Unary:
        put(raw, ref_code(pos, e.a));
        break;
    case Constant:
        put(raw, e.a);
        break;
    case Projection:
        put(raw, e.b);
        put(raw, ref_code(pos, e.a));
        break;
    default:
        break;
    }
}
static Event get_event(const Bytes &raw, size_t &off, U pos) {
    require(off < raw.size(), "missing opcode");
    Event e{static_cast<Kind>(raw[off++])};
    switch (e.kind) {
    case Triple:
        e.c = ref_value(pos, get(raw, off));
        [[fallthrough]];
    case Pair:
        e.b = ref_value(pos, get(raw, off));
        [[fallthrough]];
    case Unary:
        e.a = ref_value(pos, get(raw, off));
        break;
    case Constant:
        e.a = get(raw, off);
        break;
    case Projection:
        e.b = get(raw, off);
        e.a = ref_value(pos, get(raw, off));
        break;
    case Atom:
    case Declaration:
        break;
    default:
        throw std::runtime_error("unrecognized dependency opcode");
    }
    return e;
}
static void make_index(const fs::path &dir) {
    std::ofstream out(dir / "edges.zst", std::ios::binary);
    out.exceptions(std::ios::badbit | std::ios::failbit);
    Bytes raw;
    raw.reserve(8 << 20);
    U start_expr = 0, start_decl = 0, expr = 0, decl = 0, events = 0;
    auto flush = [&] {
        if (events == 0)
            return;
        Bytes compressed(ZSTD_compressBound(raw.size()));
        size_t size =
            ZSTD_compress(compressed.data(), compressed.size(), raw.data(), raw.size(), 2);
        require(!ZSTD_isError(size), "edge compression failed");
        for (U x : {start_expr, start_decl, events, U(raw.size()), U(size)})
            write_u(out, x);
        out.write(reinterpret_cast<char *>(compressed.data()), size);
        raw.clear();
        start_expr = expr;
        start_decl = decl;
        events = 0;
    };
    std::string line;
    while (std::getline(std::cin, line)) {
        auto k = first_key(line);
        if (non_expr(k))
            continue;
        if (decl_key(k)) {
            put_event(raw, {Declaration}, expr);
            decl++;
        } else {
            require(field(line, "\"ie\":") == expr, "nonsequential expression id");
            put_event(raw, expr_event(line, expr_key(line, k)), expr++);
        }
        if (++events == (1u << 19))
            flush();
    }
    require(std::cin.eof(), "input read failed");
    flush();
    std::ofstream totals(dir / "totals.txt");
    totals << expr << " " << decl << "\n";
    std::cerr << expr << " expressions; " << decl << " declaration records\n";
}
struct Bits {
    U count;
    std::vector<uint64_t> words;
    std::vector<U> prefix;
    uint64_t changes = 0;
    explicit Bits(U n) : count(n), words((uint64_t(n) + 63) / 64) {}
    bool has(U n) const {
        require(n < count, "out-of-range bit");
        return (words[n / 64] >> (n % 64)) & 1;
    }
    void add(U n) {
        if (!has(n)) {
            words[n / 64] |= uint64_t(1) << (n % 64);
            ++changes;
        }
    }
    void save(const fs::path &p) const {
        std::ofstream o(p, std::ios::binary);
        write_u(o, count);
        o.write((const char *)words.data(), words.size() * 8);
        require(bool(o), "bitset write");
    }
    static Bits load(const fs::path &p) {
        std::ifstream i(p, std::ios::binary);
        Bits b(read_u(i));
        require(bool(i.read((char *)b.words.data(), b.words.size() * 8)), "truncated bitset");
        return b;
    }
    void ranks() {
        prefix.resize(words.size());
        U n = 0;
        for (size_t i = 0; i < words.size(); ++i) {
            prefix[i] = n;
            n += std::popcount(words[i]);
        }
        changes = n;
    }
    U rank(U n) const {
        require(has(n), "attempt to emit dangling expression");
        return prefix[n / 64] + std::popcount(words[n / 64] & ((uint64_t(1) << (n % 64)) - 1));
    }
};
static std::vector<U> read_words(const fs::path &p) {
    size_t size = fs::file_size(p);
    require(size % 4 == 0, "bad integer table");
    std::vector<U> w(size / 4);
    std::ifstream f(p, std::ios::binary);
    require(bool(f.read((char *)w.data(), size)), "table read");
    return w;
}
struct Block {
    std::streamoff offset;
    U expr, decl, records, raw, compressed;
};
static std::vector<Block> blocks(std::ifstream &f) {
    std::vector<Block> result;
    while (f.peek() != std::char_traits<char>::eof()) {
        Block b{};
        b.expr = read_u(f);
        b.decl = read_u(f);
        b.records = read_u(f);
        b.raw = read_u(f);
        b.compressed = read_u(f);
        b.offset = f.tellg();
        result.push_back(b);
        f.seekg(b.compressed, std::ios::cur);
    }
    f.clear();
    return result;
}
static std::vector<size_t> offsets(const std::vector<U> &table, U expected) {
    std::vector<size_t> result;
    size_t p = 0;
    while (p < table.size()) {
        result.push_back(p);
        require(p + 4 <= table.size(), "truncated declaration header");
        p += 4 + table[p] + table[p + 1] + table[p + 2];
    }
    require(p == table.size() && result.size() == expected, "declaration table mismatch");
    return result;
}
static void mark(const fs::path &dir, const fs::path &output, bool merge,
                 const fs::path &whole = {}, U part = 0, U parts = 0, bool type_only = false) {
    fs::create_directories(output);
    fs::remove(output / "dictionary.bits");
    U nx, nd;
    std::ifstream totals(dir / "totals.txt");
    require(bool(totals >> nx >> nd), "missing index");
    auto canon = read_words(dir / "canonical.bin"), table = read_words(dir / "declarations.bin");
    auto entry = offsets(table, nd);
    Bits names(canon.size()), exprs(nx), decls(nd);
    Bits stubs(nd);
    U begin = 0, end = nd;
    std::vector<uint8_t> theorem;
    if (parts || type_only) {
        std::ifstream kinds(dir / "declaration-kinds.bin", std::ios::binary);
        theorem.resize(nd);
        require(bool(kinds.read(reinterpret_cast<char *>(theorem.data()), nd)),
                "missing declaration kinds");
        begin = nd;
        if (parts) {
            require(part < parts && parts <= nd, "invalid shard");
            begin = uint64_t(nd) * part / parts;
            end = uint64_t(nd) * (part + 1) / parts;
            auto full = Bits::load(whole / "decls.bits");
            require(full.count == nd, "wrong parent selection");
            for (U d = begin; d < end; ++d) {
                if (full.has(d))
                    names.add(table[entry[d] + 4]);
            }
        }
    }
    U root;
    while (std::cin >> root)
        names.add(root);
    require(std::cin.eof() && names.changes > 0, "invalid or empty root list");
    std::ifstream edgefile(dir / "edges.zst", std::ios::binary);
    auto pages = blocks(edgefile);
    unsigned passes = 0;
    uint64_t delta;
    do {
        uint64_t before = names.changes + exprs.changes + decls.changes;
        for (auto it = pages.rbegin(); it != pages.rend(); ++it) {
            const auto &b = *it;
            Bytes packed(b.compressed), raw(b.raw);
            edgefile.seekg(b.offset);
            require(bool(edgefile.read((char *)packed.data(), packed.size())), "edge read");
            require(ZSTD_decompress(raw.data(), raw.size(), packed.data(), packed.size()) ==
                        raw.size(),
                    "edge decompression");
            std::vector<Event> events;
            events.reserve(b.records);
            size_t off = 0;
            U ex = b.expr, dc = b.decl;
            for (U i = 0; i < b.records; ++i) {
                auto ev = get_event(raw, off, ex);
                events.push_back(ev);
                if (ev.kind == Declaration)
                    ++dc;
                else
                    ++ex;
            }
            require(off == raw.size(), "edge block trailing bytes");
            for (auto j = events.rbegin(); j != events.rend(); ++j) {
                const auto &e = *j;
                if (e.kind == Declaration) {
                    --dc;
                    size_t p = entry[dc];
                    U nn = table[p], ne = table[p + 1], nr = table[p + 2], alt = table[p + 3];
                    p += 4;
                    bool use = false;
                    for (U k = 0; k < nn; ++k)
                        use |= names.has(table[p + k]);
                    if (!use)
                        continue;
                    decls.add(dc);
                    for (U k = 0; k < nn; ++k)
                        names.add(table[p++]);
                    bool stub = (parts || type_only) && dc < begin && theorem[dc];
                    if (stub)
                        stubs.add(dc);
                    for (U k = 0; k < ne; ++k) {
                        U x = table[p++];
                        if (stub && k == 1)
                            continue;
                        exprs.add(merge && alt && k == 1 ? alt : x);
                    }
                    for (U k = 0; k < nr; ++k)
                        names.add(table[p++]);
                } else {
                    --ex;
                    if (!exprs.has(ex))
                        continue;
                    switch (e.kind) {
                    case Triple:
                        exprs.add(e.c);
                        [[fallthrough]];
                    case Pair:
                        exprs.add(e.b);
                        [[fallthrough]];
                    case Unary:
                        exprs.add(e.a);
                        break;
                    case Constant:
                        names.add(merge ? canon.at(e.a) : e.a);
                        break;
                    case Projection:
                        exprs.add(e.a);
                        names.add(e.b);
                        break;
                    default:
                        break;
                    }
                }
            }
        }
        delta = names.changes + exprs.changes + decls.changes - before;
        ++passes;
        std::cerr << "pass " << passes << ": " << decls.changes << " records, " << exprs.changes
                  << " expressions\n";
    } while (delta);
    names.save(output / "names.bits");
    exprs.save(output / "exprs.bits");
    decls.save(output / "decls.bits");
    if (parts || type_only) {
        stubs.save(output / "stubs.bits");
        std::ofstream cut(output / "cut.txt");
        cut << part << " " << parts << " " << begin << " " << end << " " << stubs.changes << "\n";
    } else {
        fs::remove(output / "stubs.bits");
        fs::remove(output / "cut.txt");
    }
    std::ofstream m(output / "mode.txt");
    m << merge << "\n";
}
struct Edit {
    size_t pos, end;
    U value;
};
static Edit edit(std::string_view line, std::string_view key, U value) {
    size_t p = field_pos(line, key), e = p;
    while (e < line.size() && line[e] >= '0' && line[e] <= '9')
        ++e;
    require(e > p, "expected numeric value");
    return {p, e, value};
}
static void edited(const std::string &line, std::vector<Edit> &edits) {
    std::sort(edits.begin(), edits.end(), [](auto a, auto b) { return a.pos < b.pos; });
    size_t p = 0;
    for (auto e : edits) {
        require(p <= e.pos, "overlapping fields");
        std::cout.write(line.data() + p, e.pos - p);
        std::cout << e.value;
        p = e.end;
    }
    std::cout.write(line.data() + p, line.size() - p);
    std::cout.put('\n');
}
static void rename_fields(std::string_view line, std::string_view key, bool array, const Bits &dict,
                          std::vector<Edit> &edits) {
    size_t start = 0;
    while ((start = line.find(key, start)) != line.npos) {
        size_t pos = start + key.size();
        start = pos;
        if (array) {
            if (line[pos] != '[')
                throw std::runtime_error("invalid name array");
            ++pos;
        }
        while (pos < line.size() && line[pos] >= '0' && line[pos] <= '9') {
            size_t end = pos;
            while (end < line.size() && line[end] >= '0' && line[end] <= '9')
                ++end;
            U old = number(line.substr(pos, end - pos));
            edits.push_back({pos, end, dict.rank(old)});
            if (!array || line[end] != ',')
                break;
            pos = end + 1;
        }
    }
}
static void rename_declaration(std::string_view line, const Bits &dict, std::vector<Edit> &edits) {
    for (auto key : {"\"name\":", "\"induct\":", "\"ctor\":"})
        rename_fields(line, key, false, dict, edits);
    for (auto key : {"\"levelParams\":", "\"all\":", "\"ctors\":"})
        rename_fields(line, key, true, dict, edits);
}
static void emit(const fs::path &dir, const fs::path &selection) {
    auto exprs = Bits::load(selection / "exprs.bits"), decls = Bits::load(selection / "decls.bits");
    exprs.ranks();
    bool merge;
    std::ifstream mode(selection / "mode.txt");
    require(bool(mode >> merge), "missing mode");
    auto canon = read_words(dir / "canonical.bin"), table = read_words(dir / "declarations.bin");
    auto entry = offsets(table, decls.count);
    auto stubs =
        fs::exists(selection / "stubs.bits") ? Bits::load(selection / "stubs.bits") : Bits(0);
    auto dict = fs::exists(selection / "dictionary.bits")
                    ? Bits::load(selection / "dictionary.bits")
                    : Bits(0);
    if (dict.count)
        dict.ranks();
    std::string line;
    std::vector<Edit> edits;
    edits.reserve(16);
    U dc = 0, ex = 0;
    while (std::getline(std::cin, line)) {
        auto k = first_key(line);
        edits.clear();
        if (non_expr(k)) {
            if (dict.count && k == "in") {
                U name = field(line, "\"in\":");
                if (!dict.has(name))
                    continue;
                edits.push_back(edit(line, "\"in\":", dict.rank(name)));
                edits.push_back(edit(line, "\"pre\":", dict.rank(field(line, "\"pre\":"))));
            } else if (dict.count && (k == "il" || k == "param")) {
                rename_fields(line, "\"param\":", false, dict, edits);
            }
            edited(line, edits);
            continue;
        }
        if (decl_key(k)) {
            U cur = dc++;
            if (!decls.has(cur))
                continue;
            size_t p = entry[cur];
            U alt = table[p + 3];
            if (stubs.count && stubs.has(cur)) {
                require(k == "thm", "only a theorem can cross a verification cut");
                const auto from = field_pos(line, "\"levelParams\":");
                const auto to = line.find(']', from);
                require(to != line.npos && line[from] == '[',
                        "invalid theorem universe parameters");
                std::string axiom =
                    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":" +
                    line.substr(from, to - from + 1) +
                    ",\"name\":" + std::to_string(field(line, "\"name\":")) +
                    ",\"type\":" + std::to_string(exprs.rank(field(line, "\"type\":"))) + "}}";
                if (dict.count)
                    rename_declaration(axiom, dict, edits);
                edited(axiom, edits);
                continue;
            }
            if (dict.count)
                rename_declaration(line, dict, edits);
            // These are the only expression-valued fields in a declaration, including inductive
            // rules.
            for (auto key : {std::string_view("\"type\":"), std::string_view("\"value\":"),
                             std::string_view("\"rhs\":")}) {
                size_t start = 0;
                while ((start = line.find(key, start)) != line.npos) {
                    auto tail = std::string_view(line).substr(start);
                    U old = number(tail.substr(key.size()));
                    U changed = merge && k == "thm" && key == "\"value\":" && alt ? alt : old;
                    auto e = edit(tail, key, exprs.rank(changed));
                    edits.push_back({start + e.pos, start + e.end, e.value});
                    start += e.end;
                }
            }
        } else {
            U cur = ex++;
            if (!exprs.has(cur))
                continue;
            k = expr_key(line, k);
            edits.push_back(edit(line, "\"ie\":", exprs.rank(cur)));
            auto child = [&](std::string_view key) {
                edits.push_back(edit(line, key, exprs.rank(field(line, key))));
            };
            if (k == "app") {
                child("\"fn\":");
                child("\"arg\":");
            } else if (k == "lam" || k == "forallE" || k == "letE") {
                child("\"type\":");
                child("\"body\":");
                if (k == "letE")
                    child("\"value\":");
            } else if (k == "proj")
                child("\"struct\":");
            else if (k == "mdata")
                child("\"expr\":");
            else if (k == "const" && (merge || dict.count)) {
                U n = field(line, "\"name\":");
                U to = merge ? canon.at(n) : n;
                if (dict.count)
                    to = dict.rank(to);
                if (to != n)
                    edits.push_back(edit(line, "\"name\":", to));
            }
            if (dict.count) {
                if (k == "lam" || k == "forallE" || k == "letE")
                    edits.push_back(edit(line, "\"name\":", 0));
                if (k == "proj")
                    rename_fields(line, "\"typeName\":", false, dict, edits);
                require(k != "mdata", "metadata unsupported in dictionary mode");
            }
        }
        edited(line, edits);
    }
    require(ex == exprs.count && dc == decls.count && std::cin.eof() && std::cout.good(),
            "input or output incomplete");
}
#include "intern.hpp"

int main(int argc, char **argv) {
    try {
        require(std::endian::native == std::endian::little, "little endian required");
        std::ios::sync_with_stdio(false);
        std::cin.tie(nullptr);
        require(argc >= 3,
                "usage: slice index DIR | mark DIR SELECTION plain|share | emit DIR SELECTION");
        std::string action = argv[1];
        if ((action == "intern" || action == "measure-intern") && argc == 3) {
            intern(std::cerr, number(argv[2]), action == "intern");
        } else if (action == "index" && argc == 3)
            make_index(argv[2]);
        else if (action == "mark" && argc == 5) {
            std::string m = argv[4];
            require(m == "plain" || m == "share", "invalid mode");
            mark(argv[2], argv[3], m == "share");
        } else if (action == "types" && argc == 4)
            mark(argv[2], argv[3], false, {}, 0, 0, true);
        else if ((action == "shard" || action == "shard-plain") && argc == 7) {
            U n = number(argv[6]);
            require(n > 0, "empty partition");
            mark(argv[2], argv[4], action == "shard", argv[3], number(argv[5]), n);
        } else if (action == "emit" && argc == 4)
            emit(argv[2], argv[3]);
        else
            throw std::runtime_error("invalid command");
        return 0;
    } catch (const std::exception &e) {
        std::cerr << e.what() << "\n";
        return 1;
    }
}
