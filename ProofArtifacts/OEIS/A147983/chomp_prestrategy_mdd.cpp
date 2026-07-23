// Exact separated symbolic strategy experiment for OEIS A147983 / 10 x 42 Chomp.
//
// The old checker memoized (source-P-node, set-of-reply-candidates) together.
// This experiment first builds a deterministic strategy diagram for
//
//   Pre(P) = { q | some legal bite from q lands in the exact P-language },
//
// and only then traverses each first-move image of P against that diagram.
// Candidate-set hashes are only memo-table accelerators; every collision is
// resolved by exact structural comparison.

#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

struct Node { uint32_t offset, length; };
struct Layer { std::vector<Node> nodes; std::vector<uint32_t> transitions; };

struct MDD {
    uint64_t words = 0;
    uint32_t rows = 0, width = 0, root = 0;
    std::array<Layer, 10> layer;

    explicit MDD(const std::string& path) {
        std::ifstream in(path, std::ios::binary);
        if (!in) throw std::runtime_error("cannot open MDD");
        char magic[8];
        uint32_t reserved = 0;
        in.read(magic, 8);
        in.read(reinterpret_cast<char*>(&words), 8);
        in.read(reinterpret_cast<char*>(&rows), 4);
        in.read(reinterpret_cast<char*>(&width), 4);
        in.read(reinterpret_cast<char*>(&root), 4);
        in.read(reinterpret_cast<char*>(&reserved), 4);
        if (!in || std::string(magic, 8) != "CHMDD001" || rows != 10 || width != 42)
            throw std::runtime_error("bad MDD header");
        std::array<uint64_t, 10> nodes{}, transitions{};
        for (int d = 0; d < 10; ++d) {
            in.read(reinterpret_cast<char*>(&nodes[d]), 8);
            in.read(reinterpret_cast<char*>(&transitions[d]), 8);
        }
        for (int d = 0; d < 10; ++d) {
            if (nodes[d] > UINT32_MAX || transitions[d] > UINT32_MAX)
                throw std::runtime_error("MDD layer too large");
            layer[d].nodes.resize(nodes[d]);
            layer[d].transitions.resize(transitions[d]);
            for (Node& node : layer[d].nodes) {
                in.read(reinterpret_cast<char*>(&node.offset), 4);
                in.read(reinterpret_cast<char*>(&node.length), 4);
                if (static_cast<uint64_t>(node.offset) + node.length > transitions[d])
                    throw std::runtime_error("bad node span");
            }
            in.read(reinterpret_cast<char*>(layer[d].transitions.data()),
                    static_cast<std::streamsize>(transitions[d] * 4));
        }
        if (!in) throw std::runtime_error("truncated MDD");
        if (root >= layer[0].nodes.size()) throw std::runtime_error("bad root");
    }

    int32_t step(int depth, uint32_t node, uint8_t symbol) const {
        if (depth == 10) return -1;
        const Node& n = layer[depth].nodes.at(node);
        uint32_t lo = n.offset, hi = n.offset + n.length;
        while (lo < hi) {
            uint32_t mid = lo + (hi - lo) / 2;
            uint32_t packed = layer[depth].transitions[mid];
            uint8_t s = static_cast<uint8_t>(packed & 63U);
            if (s < symbol) lo = mid + 1; else hi = mid;
        }
        if (lo == n.offset + n.length) return -1;
        uint32_t packed = layer[depth].transitions[lo];
        if ((packed & 63U) != symbol) return -1;
        return static_cast<int32_t>(packed >> 6);
    }

    bool accepts(const std::array<uint8_t, 10>& word) const {
        uint32_t node = root;
        for (int d = 0; d < 10; ++d) {
            int32_t next = step(d, node, word[d]);
            if (next < 0) return false;
            node = static_cast<uint32_t>(next);
        }
        return true;
    }
};

struct MoveTemplate {
    uint8_t row, target;
};

static std::vector<MoveTemplate> templates() {
    std::vector<MoveTemplate> out;
    for (int row = 0; row < 10; ++row) {
        int low = row == 0 ? 1 : 0;
        for (int target = low; target < 42; ++target)
            out.push_back({static_cast<uint8_t>(row), static_cast<uint8_t>(target)});
    }
    return out;
}

// phase=255 means that the bite row has already been consumed.
struct Candidate {
    uint8_t phase, target;
    uint16_t origin;
    uint32_t node;
};

static bool semantic_less(const Candidate& a, const Candidate& b) {
    if (a.phase != b.phase) return a.phase < b.phase;
    if (a.target != b.target) return a.target < b.target;
    if (a.node != b.node) return a.node < b.node;
    return a.origin < b.origin;
}

static bool semantic_equal(const Candidate& a, const Candidate& b) {
    return a.phase == b.phase && a.target == b.target && a.node == b.node;
}

static void normalize(std::vector<Candidate>& xs) {
    std::sort(xs.begin(), xs.end(), semantic_less);
    size_t out = 0;
    for (size_t i = 0; i < xs.size();) {
        size_t j = i + 1;
        Candidate best = xs[i];
        while (j < xs.size() && semantic_equal(xs[i], xs[j])) {
            if (xs[j].origin < best.origin) best.origin = xs[j].origin;
            ++j;
        }
        xs[out++] = best;
        i = j;
    }
    xs.resize(out);
}

static uint64_t mix(uint64_t x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    x ^= x >> 31; return x;
}

static uint64_t candidate_hash(uint8_t depth, uint8_t max_symbol,
                               const std::vector<Candidate>& xs) {
    uint64_t h = mix((static_cast<uint64_t>(depth) << 8) | max_symbol);
    for (const Candidate& c : xs) {
        uint64_t a = (static_cast<uint64_t>(c.phase) << 56) |
                     (static_cast<uint64_t>(c.target) << 48) |
                     (static_cast<uint64_t>(c.origin) << 32) | c.node;
        h = mix(h ^ mix(a + 0x9e3779b97f4a7c15ULL));
    }
    return h;
}

struct RawMemoEntry {
    uint8_t depth, max_symbol;
    std::vector<Candidate> candidates;
    uint32_t strategy_state;
};

struct StrategyState {
    uint8_t depth, max_symbol;
    std::array<int32_t, 43> next{};
    int32_t witness = -1;
};

static uint64_t signature_hash(uint8_t depth, uint8_t max_symbol,
                               const std::array<int32_t, 43>& next, int32_t witness) {
    uint64_t h = mix((static_cast<uint64_t>(depth) << 40) |
                     (static_cast<uint64_t>(max_symbol) << 32) |
                     static_cast<uint32_t>(witness + 1));
    for (int32_t x : next)
        h = mix(h ^ mix(static_cast<uint64_t>(static_cast<uint32_t>(x + 1)) +
                        0x9e3779b97f4a7c15ULL));
    return h;
}

class PreStrategyBuilder {
public:
    PreStrategyBuilder(const MDD& mdd, uint64_t raw_limit)
        : A(mdd), state_limit(raw_limit), moves(templates()) {}

    uint32_t build_root() {
        std::vector<Candidate> initial;
        initial.reserve(moves.size());
        for (uint16_t id = 0; id < moves.size(); ++id) {
            const MoveTemplate m = moves[id];
            initial.push_back({m.row, m.target, id, A.root});
        }
        normalize(initial);
        root = build(0, 42, std::move(initial));
        return root;
    }

    const StrategyState& state(uint32_t id) const { return states.at(id); }
    uint64_t raw_state_count() const { return raw_states; }
    uint64_t strategy_state_count() const { return states.size(); }
    uint64_t max_candidate_count() const { return max_candidates; }
    uint32_t root_id() const { return root; }
    const std::vector<MoveTemplate>& move_templates() const { return moves; }

private:
    const MDD& A;
    uint64_t state_limit;
    std::vector<MoveTemplate> moves;
    uint32_t root = 0;
    uint64_t raw_states = 0, max_candidates = 0;
    std::vector<StrategyState> states;
    std::unordered_map<uint64_t, std::vector<RawMemoEntry>> raw_memo;
    std::unordered_map<uint64_t, std::vector<uint32_t>> canonical_memo;

    bool same_raw(const RawMemoEntry& e, uint8_t depth, uint8_t max_symbol,
                  const std::vector<Candidate>& xs) const {
        if (e.depth != depth || e.max_symbol != max_symbol ||
            e.candidates.size() != xs.size()) return false;
        for (size_t i = 0; i < xs.size(); ++i) {
            const Candidate& a = e.candidates[i];
            const Candidate& b = xs[i];
            if (a.phase != b.phase || a.target != b.target ||
                a.origin != b.origin || a.node != b.node) return false;
        }
        return true;
    }

    std::vector<Candidate> advance(int depth, uint8_t qsymbol,
                                   const std::vector<Candidate>& input) const {
        std::vector<Candidate> out;
        out.reserve(input.size());
        for (Candidate c : input) {
            uint8_t rsymbol = qsymbol;
            if (c.phase == 255) {
                rsymbol = std::min<uint8_t>(qsymbol, c.target);
            } else if (depth < c.phase) {
                rsymbol = qsymbol;
            } else if (depth == c.phase) {
                if (qsymbol <= c.target) continue;
                rsymbol = c.target;
                c.phase = 255;
            } else {
                throw std::runtime_error("uncanonicalized reply phase");
            }
            int32_t next = A.step(depth, c.node, rsymbol);
            if (next < 0) continue;
            c.node = static_cast<uint32_t>(next);
            out.push_back(c);
        }
        normalize(out);
        return out;
    }

    bool same_signature(const StrategyState& s, uint8_t depth, uint8_t max_symbol,
                        const std::array<int32_t, 43>& next, int32_t witness) const {
        return s.depth == depth && s.max_symbol == max_symbol &&
               s.next == next && s.witness == witness;
    }

    uint32_t canonicalize(uint8_t depth, uint8_t max_symbol,
                          const std::array<int32_t, 43>& next, int32_t witness) {
        uint64_t h = signature_hash(depth, max_symbol, next, witness);
        auto& bucket = canonical_memo[h];
        for (uint32_t id : bucket)
            if (same_signature(states[id], depth, max_symbol, next, witness)) return id;
        uint32_t id = static_cast<uint32_t>(states.size());
        states.push_back({depth, max_symbol, next, witness});
        bucket.push_back(id);
        return id;
    }

    uint32_t build(uint8_t depth, uint8_t max_symbol, std::vector<Candidate> xs) {
        if (xs.empty()) throw std::runtime_error("empty candidate state");
        max_candidates = std::max<uint64_t>(max_candidates, xs.size());
        uint64_t h = candidate_hash(depth, max_symbol, xs);
        auto it = raw_memo.find(h);
        if (it != raw_memo.end()) {
            for (const RawMemoEntry& e : it->second)
                if (same_raw(e, depth, max_symbol, xs)) return e.strategy_state;
        }
        if (++raw_states > state_limit)
            throw std::runtime_error("pre-strategy raw-state limit exceeded");
        if ((raw_states % 100000) == 0)
            std::cerr << "raw_states=" << raw_states << " strategy_states=" << states.size()
                      << " depth=" << static_cast<int>(depth)
                      << " candidates=" << xs.size() << "\n";

        std::array<int32_t, 43> next;
        next.fill(-1);
        int32_t witness = -1;
        if (depth == 10) {
            witness = xs.front().origin;
        } else {
            for (uint8_t symbol = 0; symbol <= max_symbol; ++symbol) {
                std::vector<Candidate> child = advance(depth, symbol, xs);
                if (!child.empty())
                    next[symbol] = static_cast<int32_t>(build(depth + 1, symbol,
                                                              std::move(child)));
            }
        }
        uint32_t id = canonicalize(depth, max_symbol, next, witness);
        raw_memo[h].push_back({depth, max_symbol, std::move(xs), id});
        return id;
    }
};

struct ProductKey {
    uint8_t depth;
    uint32_t source, strategy;
};

static uint64_t product_hash(const ProductKey& k) {
    return mix((static_cast<uint64_t>(k.depth) << 56) |
               (static_cast<uint64_t>(k.source) << 28) | k.strategy);
}

class InclusionChecker {
public:
    InclusionChecker(const MDD& mdd, const PreStrategyBuilder& strategy,
                     uint64_t product_limit)
        : A(mdd), S(strategy), limit(product_limit) {}

    bool check_all() {
        verify_roots();
        const auto& moves = S.move_templates();
        uint64_t total = 0;
        for (size_t i = 0; i < moves.size(); ++i) {
            memo.clear(); states.clear(); prefix.fill(0); counterexample.fill(0);
            first = moves[i];
            bool ok = visit(0, A.root, S.root_id());
            std::cout << "first=" << static_cast<int>(first.row) << ','
                      << static_cast<int>(first.target) << " product_states="
                      << states.size() << " result=" << (ok ? "closed" : "counterexample")
                      << "\n";
            total += states.size();
            if (!ok) {
                std::cout << "counterexample=";
                for (int d = 0; d < 10; ++d) {
                    if (d) std::cout << ',';
                    std::cout << static_cast<int>(counterexample[d]);
                }
                std::cout << "\n";
                return false;
            }
        }
        std::cout << "ALL_FIRST_MOVE_IMAGES_INCLUDED total_product_states=" << total << "\n";
        return true;
    }

private:
    const MDD& A;
    const PreStrategyBuilder& S;
    uint64_t limit;
    MoveTemplate first{};
    std::array<uint8_t, 10> prefix{}, counterexample{};
    std::vector<ProductKey> states;
    std::unordered_map<uint64_t, std::vector<uint32_t>> memo;

    void verify_roots() const {
        const std::array<std::array<uint8_t, 10>, 3> roots = {{
            {{42,42,42,42,35,35,35,35,35,35}},
            {{42,42,42,42,42,42,29,29,29,29}},
            {{42,42,42,42,42,42,42,25,25,25}}
        }};
        for (const auto& root : roots)
            if (!A.accepts(root)) throw std::runtime_error("target root absent from P MDD");
    }

    bool same(const ProductKey& a, const ProductKey& b) const {
        return a.depth == b.depth && a.source == b.source && a.strategy == b.strategy;
    }

    bool seen(const ProductKey& k) const {
        uint64_t h = product_hash(k);
        auto it = memo.find(h);
        if (it == memo.end()) return false;
        for (uint32_t id : it->second) if (same(states[id], k)) return true;
        return false;
    }

    void remember(const ProductKey& k) {
        if (states.size() >= limit) throw std::runtime_error("product-state limit exceeded");
        uint64_t h = product_hash(k);
        uint32_t id = static_cast<uint32_t>(states.size());
        states.push_back(k);
        memo[h].push_back(id);
    }

    void complete_source(int depth, uint32_t node) {
        for (int d = depth; d < 10; ++d) {
            const Node& n = A.layer[d].nodes.at(node);
            if (!n.length) throw std::runtime_error("dead source node");
            uint32_t packed = A.layer[d].transitions[n.offset];
            counterexample[d] = static_cast<uint8_t>(packed & 63U);
            node = packed >> 6;
        }
    }

    bool visit(uint8_t depth, uint32_t source, uint32_t strategy) {
        if (depth == 10) return true;
        ProductKey key{depth, source, strategy};
        if (seen(key)) return true;
        const Node& n = A.layer[depth].nodes.at(source);
        const StrategyState& ss = S.state(strategy);
        for (uint32_t k = 0; k < n.length; ++k) {
            uint32_t packed = A.layer[depth].transitions[n.offset + k];
            uint8_t psymbol = static_cast<uint8_t>(packed & 63U);
            uint32_t source_next = packed >> 6;
            if (depth == first.row && psymbol <= first.target) continue;
            uint8_t qsymbol = depth < first.row
                ? psymbol : std::min<uint8_t>(psymbol, first.target);
            prefix[depth] = psymbol;
            int32_t strategy_next = ss.next[qsymbol];
            if (strategy_next < 0) {
                counterexample = prefix;
                complete_source(depth + 1, source_next);
                return false;
            }
            if (!visit(depth + 1, source_next, static_cast<uint32_t>(strategy_next)))
                return false;
        }
        remember(key);
        return true;
    }
};

int main(int argc, char** argv) {
    try {
        if (argc < 2 || argc > 4) {
            std::cerr << "usage: " << argv[0]
                      << " P.mdd [RAW_STATE_LIMIT] [PRODUCT_STATE_LIMIT]\n";
            return 2;
        }
        uint64_t raw_limit = argc >= 3 ? std::stoull(argv[2]) : 5000000ULL;
        uint64_t product_limit = argc >= 4 ? std::stoull(argv[3]) : 5000000ULL;
        MDD mdd(argv[1]);
        PreStrategyBuilder strategy(mdd, raw_limit);
        strategy.build_root();
        std::cout << "PRE_STRATEGY_BUILT raw_states=" << strategy.raw_state_count()
                  << " strategy_states=" << strategy.strategy_state_count()
                  << " max_candidates=" << strategy.max_candidate_count() << "\n";
        InclusionChecker checker(mdd, strategy, product_limit);
        return checker.check_all() ? 0 : 1;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 3;
    }
}
