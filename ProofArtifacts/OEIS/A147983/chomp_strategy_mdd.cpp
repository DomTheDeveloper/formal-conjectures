// Exact symbolic checker for two-ply closure of the Chomp P-position MDD.
//
// For every fixed legal first move template, this program traverses the P-language while carrying
// the determinized set of all legal reply templates whose resulting position can still be in P.
// A terminal state with no live reply is an explicit counterexample. Hashes only select memo
// buckets; memoized states are compared exactly.

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
    std::array<Layer,10> layer;

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
        if (!in || std::string(magic,8) != "CHMDD001" || rows != 10 || width != 42)
            throw std::runtime_error("bad MDD header");
        std::array<uint64_t,10> nodes{}, transitions{};
        for (int d=0; d<10; ++d) {
            in.read(reinterpret_cast<char*>(&nodes[d]),8);
            in.read(reinterpret_cast<char*>(&transitions[d]),8);
        }
        for (int d=0; d<10; ++d) {
            if (nodes[d] > UINT32_MAX || transitions[d] > UINT32_MAX)
                throw std::runtime_error("MDD layer too large");
            layer[d].nodes.resize(nodes[d]);
            layer[d].transitions.resize(transitions[d]);
            for (Node& node : layer[d].nodes) {
                in.read(reinterpret_cast<char*>(&node.offset),4);
                in.read(reinterpret_cast<char*>(&node.length),4);
                if (static_cast<uint64_t>(node.offset)+node.length > transitions[d])
                    throw std::runtime_error("bad node span");
            }
            in.read(reinterpret_cast<char*>(layer[d].transitions.data()),
                    static_cast<std::streamsize>(transitions[d]*4));
        }
        if (!in) throw std::runtime_error("truncated MDD");
        if (root >= layer[0].nodes.size()) throw std::runtime_error("bad root");
    }

    int32_t step(int depth, uint32_t node, uint8_t symbol) const {
        if (depth == 10) return -1;
        const Node& n = layer[depth].nodes.at(node);
        uint32_t lo = n.offset, hi = n.offset+n.length;
        while (lo < hi) {
            uint32_t mid = lo+(hi-lo)/2;
            uint32_t packed = layer[depth].transitions[mid];
            uint8_t s = static_cast<uint8_t>(packed & 63U);
            if (s < symbol) lo = mid+1; else hi = mid;
        }
        if (lo == n.offset+n.length) return -1;
        uint32_t packed = layer[depth].transitions[lo];
        if ((packed & 63U) != symbol) return -1;
        return static_cast<int32_t>(packed >> 6);
    }

    bool accepts(const std::array<uint8_t,10>& word) const {
        uint32_t node = root;
        for (int d=0; d<10; ++d) {
            int32_t next = step(d,node,word[d]);
            if (next < 0) return false;
            node = static_cast<uint32_t>(next);
        }
        return true;
    }
};

struct MoveTemplate {
    uint8_t row, target;
    bool operator<(const MoveTemplate& o) const {
        return row < o.row || (row == o.row && target < o.target);
    }
};

static std::vector<MoveTemplate> templates() {
    std::vector<MoveTemplate> out;
    for (int row=0; row<10; ++row) {
        int low = row == 0 ? 1 : 0;
        for (int target=low; target<42; ++target)
            out.push_back({static_cast<uint8_t>(row),static_cast<uint8_t>(target)});
    }
    return out;
}

// row=255 means the reply bite row has already been processed.
struct Candidate {
    uint8_t row, target;
    uint32_t node;
    bool operator==(const Candidate& o) const {
        return row==o.row && target==o.target && node==o.node;
    }
    bool operator<(const Candidate& o) const {
        if (row != o.row) return row < o.row;
        if (target != o.target) return target < o.target;
        return node < o.node;
    }
};

static uint64_t mix(uint64_t x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    x ^= x >> 31; return x;
}

struct State {
    uint8_t depth;
    uint32_t source;
    std::vector<Candidate> candidates;
};

static uint64_t state_hash(const State& s) {
    uint64_t h = mix((static_cast<uint64_t>(s.depth)<<32)|s.source);
    for (const Candidate& c : s.candidates) {
        uint64_t x = (static_cast<uint64_t>(c.row)<<40) |
                     (static_cast<uint64_t>(c.target)<<32) | c.node;
        h = mix(h ^ mix(x + 0x9e3779b97f4a7c15ULL));
    }
    return h;
}

class Checker {
public:
    Checker(const MDD& mdd, uint64_t limit) : A(mdd), state_limit(limit), replies(templates()) {}

    bool check_all() {
        verify_roots();
        auto first_moves = templates();
        uint64_t total_states = 0;
        for (size_t index=0; index<first_moves.size(); ++index) {
            memo.clear(); states.clear(); prefix.fill(0);
            MoveTemplate first = first_moves[index];
            State initial{0,A.root,{}};
            initial.candidates.reserve(replies.size());
            for (const MoveTemplate& move : replies)
                initial.candidates.push_back({move.row,move.target,A.root});
            bool ok = visit(first, std::move(initial));
            std::cout << "first=" << static_cast<int>(first.row) << ','
                      << static_cast<int>(first.target) << " states=" << states.size()
                      << " result=" << (ok ? "closed" : "counterexample") << "\n";
            total_states += states.size();
            if (!ok) {
                std::cout << "counterexample=";
                for (int d=0; d<10; ++d) {
                    if (d) std::cout << ',';
                    std::cout << static_cast<int>(counterexample[d]);
                }
                std::cout << "\n";
                return false;
            }
        }
        std::cout << "ALL_RESPONSE_CLOSURE_CHECKS_PASSED total_states=" << total_states << "\n";
        return true;
    }

private:
    const MDD& A;
    uint64_t state_limit;
    std::vector<MoveTemplate> replies;
    std::vector<State> states;
    std::unordered_map<uint64_t,std::vector<uint32_t>> memo;
    std::array<uint8_t,10> prefix{}, counterexample{};

    void verify_roots() const {
        const std::array<std::array<uint8_t,10>,3> roots = {{
            {{42,42,42,42,35,35,35,35,35,35}},
            {{42,42,42,42,42,42,29,29,29,29}},
            {{42,42,42,42,42,42,42,25,25,25}}
        }};
        for (const auto& root : roots)
            if (!A.accepts(root)) throw std::runtime_error("target root absent from P MDD");
    }

    bool same(const State& a, const State& b) const {
        return a.depth==b.depth && a.source==b.source && a.candidates==b.candidates;
    }

    bool memoized(const State& s) const {
        uint64_t h = state_hash(s);
        auto it = memo.find(h);
        if (it == memo.end()) return false;
        for (uint32_t id : it->second) if (same(states[id],s)) return true;
        return false;
    }

    void remember(State&& s) {
        if (states.size() >= state_limit) throw std::runtime_error("strategy state limit exceeded");
        uint64_t h = state_hash(s);
        uint32_t id = static_cast<uint32_t>(states.size());
        states.push_back(std::move(s));
        memo[h].push_back(id);
    }

    std::vector<Candidate> advance_candidates(int depth, uint8_t qsymbol,
                                               const std::vector<Candidate>& input) const {
        std::vector<Candidate> out;
        out.reserve(input.size());
        for (Candidate c : input) {
            uint8_t rsymbol = qsymbol;
            if (c.row == 255) {
                rsymbol = std::min<uint8_t>(qsymbol,c.target);
            } else if (depth < c.row) {
                rsymbol = qsymbol;
            } else if (depth == c.row) {
                if (qsymbol <= c.target) continue;
                rsymbol = c.target;
                c.row = 255;
            } else {
                throw std::runtime_error("uncanonicalized reply phase");
            }
            int32_t next = A.step(depth,c.node,rsymbol);
            if (next < 0) continue;
            c.node = static_cast<uint32_t>(next);
            out.push_back(c);
        }
        std::sort(out.begin(),out.end());
        out.erase(std::unique(out.begin(),out.end()),out.end());
        return out;
    }

    void complete_source_word(int depth, uint32_t node, std::array<uint8_t,10>& word) const {
        for (int d=depth; d<10; ++d) {
            const Node& n = A.layer[d].nodes.at(node);
            if (!n.length) throw std::runtime_error("dead source MDD node");
            uint32_t packed = A.layer[d].transitions[n.offset];
            word[d] = static_cast<uint8_t>(packed & 63U);
            node = packed >> 6;
        }
    }

    bool visit(const MoveTemplate first, State state) {
        if (state.candidates.empty()) {
            counterexample = prefix;
            complete_source_word(state.depth,state.source,counterexample);
            return false;
        }
        if (state.depth == 10) return true;
        if (memoized(state)) return true;

        const Node source_node = A.layer[state.depth].nodes.at(state.source);
        for (uint32_t k=0; k<source_node.length; ++k) {
            uint32_t packed = A.layer[state.depth].transitions[source_node.offset+k];
            uint8_t psymbol = static_cast<uint8_t>(packed & 63U);
            uint32_t source_next = packed >> 6;
            if (state.depth == first.row && psymbol <= first.target) continue;
            uint8_t qsymbol = state.depth < first.row
                ? psymbol : std::min<uint8_t>(psymbol,first.target);
            prefix[state.depth] = psymbol;
            State child{static_cast<uint8_t>(state.depth+1),source_next,
                        advance_candidates(state.depth,qsymbol,state.candidates)};
            if (!visit(first,std::move(child))) return false;
        }
        remember(std::move(state));
        return true;
    }
};

int main(int argc, char** argv) {
    try {
        if (argc < 2 || argc > 3) {
            std::cerr << "usage: " << argv[0] << " P.mdd [STATE_LIMIT]\n";
            return 2;
        }
        uint64_t limit = argc == 3 ? std::stoull(argv[2]) : 2000000ULL;
        MDD mdd(argv[1]);
        Checker checker(mdd,limit);
        return checker.check_all() ? 0 : 1;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 3;
    }
}