// Reuse identical expression records. Hash collisions can evict cache entries,
// but never identify different keys. Old indices map to an earlier exact term.
struct NodeKey {
    U tag = 0;
    U a = 0;
    U b = 0;
    U c = 0;
    U d = 0;
    bool operator==(const NodeKey &) const = default;

    uint64_t hash() const {
        uint64_t h = 14695981039346656037ULL;
        for (U x : {tag, a, b, c, d})
            h = (h ^ x) * 1099511628211ULL;
        h ^= h >> 33;
        h *= 0xff51afd7ed558ccdULL;
        return h ^ (h >> 33);
    }
};

class NodeIndices {
    std::vector<uint64_t> unique_bits;
    std::vector<U> unique_before;
    std::vector<U> old_duplicates;

  public:
    U input_count = 0;
    U output_count = 0;

    U translate(U old) const {
        require(old < input_count, "invalid forward expression reference");
        U block = old / 64;
        uint64_t bit = uint64_t(1) << (old % 64);
        U ahead = unique_before[block] + std::popcount(unique_bits[block] & (bit - 1));
        if (unique_bits[block] & bit)
            return ahead;
        return old_duplicates[old - ahead];
    }

    void append(U target) {
        if (input_count % 64 == 0) {
            unique_bits.push_back(0);
            unique_before.push_back(output_count);
        }
        if (target == output_count) {
            unique_bits.back() |= uint64_t(1) << (input_count % 64);
            ++output_count;
        } else {
            require(target < output_count, "invalid shared expression index");
            old_duplicates.push_back(target);
        }
        ++input_count;
    }
};

struct KeyEntry {
    NodeKey key;
    U result = 0;
};

static U binder_info(std::string_view line) {
    auto pos = field_pos(line, "\"binderInfo\":\"");
    auto name = line.substr(pos, line.find('"', pos) - pos);
    if (name == "default")
        return 0;
    if (name == "implicit")
        return 1;
    if (name == "strictImplicit")
        return 2;
    if (name == "instImplicit")
        return 3;
    throw std::runtime_error("unknown binder annotation");
}

static NodeKey const_key(std::string_view line) {
    const auto from = field_pos(line, "\"us\":[");
    auto to = line.find(']', from);
    require(to != line.npos, "invalid constant universe list");
    NodeKey k{7, field(line, "\"name\":")};
    if (to == from)
        return k;
    auto us = line.substr(from, to - from);
    k.b = number(us);
    k.tag = 8;
    auto comma = us.find(',');
    if (comma == us.npos)
        return k;
    if (us.find(',', comma + 1) != us.npos)
        return {};
    k.tag = 9;
    k.c = number(us.substr(comma + 1));
    return k;
}

static void intern(std::ostream &counts, unsigned power, bool write_output) {
    require(power >= 10 && power <= 25, "cache exponent outside 10 through 25");
    std::vector<KeyEntry> cache(size_t(1) << power);
    NodeIndices indices;
    std::string line;
    std::vector<Edit> changes;
    changes.reserve(12);
    while (std::getline(std::cin, line)) {
        auto tag = first_key(line);
        changes.clear();
        if (non_expr(tag)) {
            if (write_output)
                std::cout << line << '\n';
            continue;
        }
        if (decl_key(tag)) {
            if (!write_output)
                continue;
            for (std::string_view key : {"\"type\":", "\"value\":", "\"rhs\":"}) {
                size_t p = 0;
                while ((p = line.find(key, p)) != line.npos) {
                    auto tail = std::string_view(line).substr(p);
                    auto e = edit(tail, key, indices.translate(field(tail, key)));
                    changes.push_back({p + e.pos, p + e.end, e.value});
                    p += e.end;
                }
            }
            edited(line, changes);
            continue;
        }
        require(field(line, "\"ie\":") == indices.input_count, "input expression order mismatch");
        const auto kind = expr_key(line, tag);
        const auto child = [&](std::string_view key) {
            U n = indices.translate(field(line, key));
            if (write_output)
                changes.push_back(edit(line, key, n));
            return n;
        };
        NodeKey key;
        if (kind == "app") {
            key = {1, child("\"fn\":"), child("\"arg\":")};
        } else if (kind == "forallE" || kind == "lam") {
            U flags = binder_info(line) << 8;
            key = {U(kind == "lam" ? 2 : 3) | flags, child("\"type\":"), child("\"body\":"),
                   field(line, "\"name\":")};
        } else if (kind == "letE") {
            auto flag = line.substr(field_pos(line, "\"nondep\":"), 4);
            require(flag == "true" || flag == "fals", "invalid let annotation");
            key = {U(flag == "true" ? 4 : 5), child("\"type\":"), child("\"value\":"),
                   child("\"body\":"), field(line, "\"name\":")};
        } else if (kind == "proj") {
            key = {6, child("\"struct\":"), field(line, "\"typeName\":"), field(line, "\"idx\":")};
        } else if (kind == "const") {
            key = const_key(line);
        } else if (kind == "mdata") {
            child("\"expr\":");
        } else {
            require(kind == "sort" || kind == "bvar" || kind == "natVal" || kind == "strVal",
                    "unknown internable expression");
        }
        U result = indices.output_count;
        if (key.tag) {
            auto &slot = cache[key.hash() & (cache.size() - 1)];
            if (slot.key == key)
                result = slot.result;
            else
                slot = {key, result};
        }
        if (write_output && result == indices.output_count) {
            changes.push_back(edit(line, "\"ie\":", result));
            edited(line, changes);
        }
        indices.append(result);
    }
    require(std::cin.eof() && std::cout.good(), "expression stream interrupted");
    counts << indices.input_count << " input expressions, " << indices.output_count
           << " distinct retained expressions, " << indices.input_count - indices.output_count
           << " shared\n";
}
