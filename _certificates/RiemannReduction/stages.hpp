// Assign each chosen declaration to a stage that contains or imports all of its dependencies.
template <class F> static void walk_reverse(const fs::path &path, F step) {
    std::ifstream file(path, std::ios::binary);
    auto index = blocks(file);
    for (auto it = index.rbegin(); it != index.rend(); ++it) {
        Bytes compressed(it->compressed), raw(it->raw);
        file.seekg(it->offset);
        require(bool(file.read((char *)compressed.data(), compressed.size())),
                "truncated edge page");
        require(ZSTD_decompress(raw.data(), raw.size(), compressed.data(), compressed.size()) ==
                    raw.size(),
                "invalid edge page");
        std::vector<Event> events;
        events.reserve(it->records);
        U x = it->expr, d = it->decl;
        size_t pos = 0;
        for (U j = 0; j < it->records; ++j) {
            auto e = get_event(raw, pos, x);
            events.push_back(e);
            if (e.kind == Declaration)
                ++d;
            else
                ++x;
        }
        require(pos == raw.size(), "incomplete page");
        for (auto e = events.rbegin(); e != events.rend(); ++e) {
            if (e->kind == Declaration)
                --d;
            else
                --x;
            step(*e, x, d);
        }
    }
}

template <class FX, class FN> static void children(const Event &e, FX expression, FN symbol) {
    switch (e.kind) {
    case Triple:
        expression(e.c);
        [[fallthrough]];
    case Pair:
        expression(e.b);
        [[fallthrough]];
    case Unary:
        expression(e.a);
        break;
    case Constant:
        symbol(e.a, true);
        break;
    case Projection:
        expression(e.a);
        symbol(e.b, false);
        break;
    default:
        break;
    }
}

// Supply the declarations that one complete proof needs beyond an independently checked base.
static void stage_extension(const fs::path &dir, const fs::path &base,
                            const fs::path &solution, const fs::path &out) {
    require(!fs::exists(base / "stubs.bits") && !fs::exists(solution / "stubs.bits"),
            "a parent proof contains temporary theorem assumptions");
    std::ifstream a(base / "mode.txt"), b(solution / "mode.txt");
    bool first, merge;
    require(bool(a >> first) && bool(b >> merge) && first == merge, "incompatible proof modes");
    auto before = Bits::load(base / "decls.bits"), after = Bits::load(solution / "decls.bits");
    require(before.count == after.count, "different original declaration counts");
    U nx, nd;
    std::ifstream totals(dir / "totals.txt");
    require(bool(totals >> nx >> nd) && nd == after.count, "different original index");
    auto canon = read_words(dir / "canonical.bin"), table = read_words(dir / "declarations.bin");
    auto entry = offsets(table, nd);
    Bits declarations(nd), available(canon.size()), names(canon.size()), expressions(nx);
    for (U d = 0; d < nd; ++d) {
        if (!before.has(d) && !after.has(d))
            continue;
        U p = entry[d], nn = table[p], ne = table[p + 1], nr = table[p + 2], alt = table[p + 3];
        bool fresh = !before.has(d);
        if (fresh)
            declarations.add(d);
        p += 4;
        for (U j = 0; j < nn; ++j) {
            U n = table[p++];
            available.add(n);
            if (fresh)
                names.add(n);
        }
        if (!fresh)
            continue;
        for (U j = 0; j < ne; ++j) {
            U x = table[p++];
            expressions.add(merge && alt && j == 1 ? alt : x);
        }
        for (U j = 0; j < nr; ++j)
            names.add(table[p++]);
    }
    walk_reverse(dir / "edges.zst", [&](const Event &e, U x, U) {
        if (e.kind == Declaration || !expressions.has(x))
            return;
        children(e, [&](U child) { expressions.add(child); },
                 [&](U n, bool rewrite) { names.add(merge && rewrite ? canon.at(n) : n); });
    });
    for (U n = 0; n < names.count; ++n)
        require(!names.has(n) || available.has(n), "extension has an unproved prerequisite");
    fs::create_directories(out);
    require(!fs::exists(out / "stubs.bits"), "use a fresh extension directory");
    fs::remove(out / "dictionary.bits");
    declarations.save(out / "decls.bits");
    expressions.save(out / "exprs.bits");
    names.save(out / "names.bits");
    std::ofstream mode(out / "mode.txt");
    mode << int(merge) << "\n";
    std::cerr << "extension: " << declarations.changes << " declarations, "
              << expressions.changes << " expression records\n";
}

static void stage_plan(const fs::path &dir, const fs::path &whole, const fs::path &out, U stages) {
    require(stages && stages <= 32, "use one to thirty-two stages");
    fs::create_directories(out);
    auto full = Bits::load(whole / "decls.bits");
    auto fullExprs = Bits::load(whole / "exprs.bits");
    const U nx = fullExprs.count, nd = full.count;
    auto table = read_words(dir / "declarations.bin"), canon = read_words(dir / "canonical.bin");
    auto entry = offsets(table, nd);
    bool merge;
    std::ifstream mode(whole / "mode.txt");
    require(bool(mode >> merge), "missing parent rewrite mode");
    const U missing = UINT32_MAX;
    std::vector<U> symbolOwner(canon.size(), missing);
    for (U d = 0; d < nd; ++d) {
        U p = entry[d], n = table[p];
        for (U j = 0; j < n; ++j)
            symbolOwner.at(table[p + 4 + j]) = d;
    }
    std::vector<uint8_t> owner(nd, 255), needed(nx, 255);
    auto primitive = std::vector<U>{};
    U name;
    while (std::cin >> name)
        primitive.push_back(name);
    require(std::cin.eof(), "invalid primitives");
    // Balance by the export's expression positions rather than its uneven declaration sizes.
    walk_reverse(dir / "edges.zst", [&](const Event &e, U x, U d) {
        if (e.kind == Declaration && full.has(d))
            owner[d] = std::min<uint64_t>(stages - 1, uint64_t(stages) * x / nx);
    });
    for (auto n : primitive) {
        auto d = symbolOwner.at(n);
        require(d != missing && full.has(d), "missing native primitive");
        owner[d] = 0;
    }
    auto references = [&](U d, auto expression, auto symbol) {
        U p = entry[d], n = table[p], ne = table[p + 1], nr = table[p + 2], alt = table[p + 3];
        p += 4 + n;
        for (U j = 0; j < ne; ++j) {
            U v = table[p++];
            expression(merge && alt && j == 1 ? alt : v);
        }
        for (U j = 0; j < nr; ++j)
            symbol(table[p++], false);
    };
    size_t changed;
    do {
        changed = 0;
        walk_reverse(dir / "edges.zst", [&](const Event &e, U x, U d) {
            uint8_t s = e.kind == Declaration ? owner[d] : needed[x];
            if (s == 255)
                return;
            auto expression = [&](U child) {
                if (s < needed[child]) {
                    needed[child] = s;
                    ++changed;
                }
            };
            auto symbol = [&](U n, bool useCanon) {
                if (merge && useCanon)
                    n = canon.at(n);
                U target = symbolOwner.at(n);
                require(target != missing && full.has(target), "symbol outside the parent article");
                if (s < owner[target]) {
                    owner[target] = s;
                    ++changed;
                }
            };
            if (e.kind == Declaration)
                references(d, expression, symbol);
            else
                children(e, expression, symbol);
        });
        std::cerr << changed << " earlier placements\n";
    } while (changed);
    std::vector<uint8_t>().swap(needed);
    std::vector<U> masks(nx);
    for (U d = 0; d < nd; ++d)
        if (owner[d] != 255) {
            auto bit = U(1) << owner[d];
            references(d, [&](U x) { masks[x] |= bit; }, [](U, bool) {});
        }
    walk_reverse(dir / "edges.zst", [&](const Event &e, U x, U) {
        if (e.kind == Declaration || !masks[x])
            return;
        U m = masks[x];
        children(e, [&](U child) { masks[child] |= m; }, [](U, bool) {});
    });
    // The union must contain every expression and declaration of the chosen proof.
    for (U x = 0; x < nx; ++x)
        require(bool(masks[x]) == fullExprs.has(x), "expression coverage differs");
    for (U d = 0; d < nd; ++d)
        require((owner[d] != 255) == full.has(d), "declaration coverage differs");
    {
        std::ofstream f(out / "owners.bin", std::ios::binary);
        f.write((char *)owner.data(), owner.size());
        require(bool(f), "owner write failed");
    }
    {
        std::ofstream f(out / "masks.bin", std::ios::binary);
        f.write((char *)masks.data(), uint64_t(nx) * sizeof(U));
        require(bool(f), "mask write failed");
    }
    std::ofstream info(out / "sizes.txt");
    info << stages << " " << nx << " " << nd << " " << merge << "\n";
    std::vector<Bits> ranks;
    for (U s = 0; s < stages; ++s)
        ranks.emplace_back(nx);
    for (U x = 0; x < nx; ++x)
        for (U m = masks[x]; m; m &= m - 1)
            ranks[std::countr_zero(m)].add(x);
    for (U s = 0; s < stages; ++s) {
        ranks[s].save(out / ("expressions-" + std::to_string(s) + ".bits"));
        std::cerr << "stage " << s << ": " << std::count(owner.begin(), owner.end(), s)
                  << " records, " << ranks[s].changes << " expressions\n";
    }
}
struct Stages {
    U count, expressions, declarations;
    bool merge;
    Bytes owners;
    std::vector<U> masks;
    explicit Stages(const fs::path &p) : masks(read_words(p / "masks.bin")) {
        std::ifstream meta(p / "sizes.txt");
        require(bool(meta >> count >> expressions >> declarations >> merge), "stage sizes missing");
        require(count && count <= 32 && masks.size() == expressions,
                "invalid stage expression masks");
        owners.resize(declarations);
        std::ifstream f(p / "owners.bin", std::ios::binary);
        require(bool(f.read((char *)owners.data(), declarations)), "invalid stage owners");
    }
};
template <class F> static void each_bit(U mask, F run) {
    while (mask) {
        run(static_cast<U>(std::countr_zero(mask)));
        mask &= mask - 1;
    }
}
template <class F>
static void name_fields(std::string_view line, std::string_view key, bool array, F action) {
    size_t pos = 0;
    while ((pos = line.find(key, pos)) != line.npos) {
        pos += key.size();
        if (array) {
            require(line[pos] == '[', "invalid name field");
            ++pos;
        }
        while (pos < line.size() && line[pos] >= '0' && line[pos] <= '9') {
            action(number(line.substr(pos)));
            while (pos < line.size() && line[pos] >= '0' && line[pos] <= '9')
                ++pos;
            if (!array || line[pos] != ',')
                break;
            ++pos;
        }
    }
}
static void stage_names(const fs::path &dir, const fs::path &plan) {
    Stages stages(plan);
    auto parents = read_words(dir / "name-parents.bin"), canon = read_words(dir / "canonical.bin");
    std::vector<U> used(parents.size());
    U all = stages.count == 32 ? UINT32_MAX : (U(1) << stages.count) - 1;
    used[0] = all;
    std::string line;
    U x = 0, d = 0;
    while (std::getline(std::cin, line)) {
        auto k = first_key(line);
        if (non_expr(k)) {
            if (k == "il" || k == "param")
                name_fields(line, "\"param\":", false, [&](U n) { used.at(n) |= all; });
        } else if (decl_key(k)) {
            auto owner = stages.owners.at(d++);
            if (owner == 255)
                continue;
            U mask = U(1) << owner;
            auto use = [&](U n) { used.at(n) |= mask; };
            for (auto key : {"\"name\":", "\"induct\":", "\"ctor\":"})
                name_fields(line, key, false, use);
            for (auto key : {"\"levelParams\":", "\"all\":", "\"ctors\":"})
                name_fields(line, key, true, use);
        } else {
            const U mask = stages.masks.at(x++);
            if (!mask)
                continue;
            k = expr_key(line, k);
            if (k == "const" || k == "lam" || k == "forallE" || k == "letE") {
                U n = field(line, "\"name\":");
                used.at(k == "const" && stages.merge ? canon.at(n) : n) |= mask;
            } else if (k == "proj")
                used.at(field(line, "\"typeName\":")) |= mask;
            else
                require(k != "mdata", "metadata names are unsupported");
        }
    }
    require(std::cin.eof() && x == stages.expressions && d == stages.declarations,
            "name scan incomplete");
    for (size_t n = used.size(); n-- > 1;)
        used.at(parents[n]) |= used[n];
    std::vector<Bits> dictionaries;
    for (U k = 0; k < stages.count; ++k)
        dictionaries.emplace_back(used.size());
    for (U n = 0; n < used.size(); ++n)
        each_bit(used[n], [&](U k) { dictionaries[k].add(n); });
    for (U k = 0; k < stages.count; ++k)
        dictionaries[k].save(plan / ("names-" + std::to_string(k) + ".bits"));
}
static void write_edits(std::ostream &out, const std::string &line, std::vector<Edit> &edits) {
    std::sort(edits.begin(), edits.end(),
              [](const Edit &a, const Edit &b) { return a.pos < b.pos; });
    size_t start = 0;
    for (const auto &e : edits) {
        require(start <= e.pos, "overlapping integer fields");
        out.write(line.data() + start, e.pos - start);
        out << e.value;
        start = e.end;
    }
    out.write(line.data() + start, line.size() - start);
    out.put('\n');
}
static void stage_emit(const fs::path &dir, const fs::path &plan, const fs::path &dest) {
    Stages stages(plan);
    auto canon = read_words(dir / "canonical.bin"), table = read_words(dir / "declarations.bin");
    auto entry = offsets(table, stages.declarations);
    std::vector<Bits> exprs, dicts;
    std::vector<std::ofstream> files;
    for (U k = 0; k < stages.count; ++k) {
        exprs.push_back(Bits::load(plan / ("expressions-" + std::to_string(k) + ".bits")));
        exprs.back().ranks();
        dicts.push_back(Bits::load(plan / ("names-" + std::to_string(k) + ".bits")));
        dicts.back().ranks();
        files.emplace_back(dest / ("stage-" + std::to_string(k) + ".ndjson"), std::ios::binary);
        require(bool(files.back()), "could not open stage output");
    }
    U x = 0, d = 0;
    U all = stages.count == 32 ? UINT32_MAX : (U(1) << stages.count) - 1;
    std::vector<Edit> edits;
    edits.reserve(24);
    std::string line;
    while (std::getline(std::cin, line)) {
        auto first = first_key(line), k = first;
        U mask = all, index = 0;
        bool expr = false, decl = false;
        if (decl_key(k)) {
            index = d++;
            auto own = stages.owners.at(index);
            if (own == 255)
                continue;
            mask = U(1) << own;
            decl = true;
        } else if (!non_expr(k)) {
            index = x++;
            mask = stages.masks.at(index);
            if (!mask)
                continue;
            k = expr_key(line, k);
            expr = true;
        } else if (k == "in") {
            index = field(line, "\"in\":");
            mask = 0;
            for (U j = 0; j < stages.count; ++j)
                if (dicts[j].has(index))
                    mask |= U(1) << j;
        }
        each_bit(mask, [&](U part) {
            auto &es = exprs[part], &ns = dicts[part];
            edits.clear();
            if (decl) {
                rename_declaration(line, ns, edits);
                U alt = stages.merge && k == "thm" ? table[entry[index] + 3] : 0;
                for (std::string_view fieldKey : {"\"type\":", "\"value\":", "\"rhs\":"}) {
                    size_t pos = 0;
                    while ((pos = line.find(fieldKey, pos)) != line.npos) {
                        auto suffix = std::string_view(line).substr(pos);
                        U n = fieldKey == "\"value\":" && alt
                                  ? alt
                                  : number(suffix.substr(fieldKey.size()));
                        auto e = edit(suffix, fieldKey, es.rank(n));
                        edits.push_back({pos + e.pos, pos + e.end, e.value});
                        pos += e.end;
                    }
                }
            } else if (expr) {
                edits.push_back(edit(line, "\"ie\":", es.rank(index)));
                auto child = [&](std::string_view key) {
                    edits.push_back(edit(line, key, es.rank(field(line, key))));
                };
                if (k == "app") {
                    child("\"fn\":");
                    child("\"arg\":");
                } else if (k == "lam" || k == "forallE" || k == "letE") {
                    child("\"type\":");
                    child("\"body\":");
                    if (k == "letE")
                        child("\"value\":");
                    rename_fields(line, "\"name\":", false, ns, edits);
                } else if (k == "proj") {
                    child("\"struct\":");
                    rename_fields(line, "\"typeName\":", false, ns, edits);
                } else if (k == "const") {
                    U n = field(line, "\"name\":");
                    edits.push_back(
                        edit(line, "\"name\":", ns.rank(stages.merge ? canon.at(n) : n)));
                } else
                    require(k != "mdata", "unexpected metadata");
            } else if (k == "in") {
                edits.push_back(edit(line, "\"in\":", ns.rank(index)));
                edits.push_back(edit(line, "\"pre\":", ns.rank(field(line, "\"pre\":"))));
            } else if (k == "il" || k == "param")
                rename_fields(line, "\"param\":", false, ns, edits);
            write_edits(files[part], line, edits);
        });
    }
    require(std::cin.eof() && x == stages.expressions && d == stages.declarations,
            "stage stream incomplete");
    for (auto &f : files) {
        f.flush();
        require(bool(f), "failed writing full stage");
    }
}
