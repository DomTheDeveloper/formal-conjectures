// Synthesize a small closed two-ply response carrier for the three 10x42 Chomp roots.
//
// The reduced P-position MDD is used only as an untrusted oracle for candidate discovery.  For each
// carrier position p, every legal opponent child q is enumerated exactly.  Legal P replies r are
// grouped across all q, and a greedy set-cover step chooses replies that cover as many q as
// possible, strongly preferring replies already present in the carrier.  The resulting explicit
// p -> q -> r mapping is a candidate Lean certificate, not trusted proof code.

#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using Position = std::array<uint8_t, 10>;

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
        const Node& n = layer[depth].nodes.at(node);
        uint32_t lo = n.offset, hi = n.offset + n.length;
        while (lo < hi) {
            const uint32_t mid = lo + (hi - lo) / 2;
            const uint32_t packed = layer[depth].transitions[mid];
            const uint8_t s = static_cast<uint8_t>(packed & 63U);
            if (s < symbol) lo = mid + 1; else hi = mid;
        }
        if (lo == n.offset + n.length) return -1;
        const uint32_t packed = layer[depth].transitions[lo];
        if ((packed & 63U) != symbol) return -1;
        return static_cast<int32_t>(packed >> 6);
    }

    bool accepts(const Position& p) const {
        uint32_t node = root;
        for (int d = 0; d < 10; ++d) {
            const int32_t next = step(d, node, p[d]);
            if (next < 0) return false;
            node = static_cast<uint32_t>(next);
        }
        return true;
    }
};

static uint64_t pack(const Position& p) {
    uint64_t z = 0;
    for (int i = 0; i < 10; ++i) z |= static_cast<uint64_t>(p[i]) << (6 * i);
    return z;
}

static Position unpack(uint64_t z) {
    Position p{};
    for (int i = 0; i < 10; ++i) p[i] = static_cast<uint8_t>((z >> (6 * i)) & 63U);
    return p;
}

static int area(const Position& p) {
    int sum = 0;
    for (uint8_t x : p) sum += x;
    return sum;
}

static std::vector<uint64_t> children(const Position& p) {
    std::vector<uint64_t> out;
    out.reserve(420);
    for (int row = 0; row < 10; ++row) {
        const int low = row == 0 ? 1 : 0;
        for (int target = low; target < p[row]; ++target) {
            Position q = p;
            for (int j = row; j < 10; ++j)
                q[j] = std::min<int>(q[j], target);
            out.push_back(pack(q));
        }
    }
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
    return out;
}

struct ReplyChoice {
    uint64_t key;
    uint32_t frequency;
    int area;
};

class Synthesizer {
public:
    Synthesizer(const MDD& mdd, uint64_t limit, bool prefer_low_area)
        : A(mdd), node_limit(limit), low_area(prefer_low_area) {}

    int run() {
        const std::array<Position, 3> roots = {{
            {{42,42,42,42,35,35,35,35,35,35}},
            {{42,42,42,42,42,42,29,29,29,29}},
            {{42,42,42,42,42,42,42,25,25,25}}
        }};
        for (const Position& root : roots) {
            if (!A.accepts(root)) throw std::runtime_error("target root absent from P MDD");
            insert_carrier(pack(root));
        }

        while (!stack.empty()) {
            const uint64_t pkey = stack.back();
            stack.pop_back();
            const Position p = unpack(pkey);
            process_position(p);
            ++processed;
            if (processed % 10000 == 0) {
                std::cerr << "processed=" << processed << " carrier=" << carrier.size()
                          << " responses=" << response_edges << " stack=" << stack.size()
                          << " max_new=" << max_new_per_position << '\n';
            }
        }

        std::cout << "COMPLETE carrier=" << carrier.size()
                  << " processed=" << processed
                  << " responses=" << response_edges
                  << " selected_new=" << selected_new
                  << " reused=" << reused
                  << " max_opponent_children=" << max_opponent_children
                  << " max_new_per_position=" << max_new_per_position
                  << " heuristic=" << (low_area ? "low-area" : "high-area") << '\n';
        return 0;
    }

private:
    const MDD& A;
    uint64_t node_limit;
    bool low_area;
    std::unordered_set<uint64_t> carrier;
    std::vector<uint64_t> stack;
    uint64_t processed = 0;
    uint64_t response_edges = 0;
    uint64_t selected_new = 0;
    uint64_t reused = 0;
    uint64_t max_opponent_children = 0;
    uint64_t max_new_per_position = 0;

    void insert_carrier(uint64_t key) {
        if (carrier.insert(key).second) {
            if (carrier.size() > node_limit) {
                std::cout << "LIMIT carrier=" << carrier.size() << " processed=" << processed
                          << " responses=" << response_edges << " stack=" << stack.size() << '\n';
                throw std::runtime_error("carrier node limit exceeded");
            }
            stack.push_back(key);
        }
    }

    void process_position(const Position& p) {
        const std::vector<uint64_t> qkeys = children(p);
        max_opponent_children = std::max<uint64_t>(max_opponent_children, qkeys.size());
        response_edges += qkeys.size();

        std::vector<std::vector<uint64_t>> options(qkeys.size());
        std::vector<uint8_t> covered(qkeys.size(), 0);
        size_t uncovered = qkeys.size();

        // Enumerate every exact legal P reply. Existing carrier members cover first.
        for (size_t qi = 0; qi < qkeys.size(); ++qi) {
            const Position q = unpack(qkeys[qi]);
            if (A.accepts(q)) throw std::runtime_error("carrier P position has a P child");
            for (uint64_t rkey : children(q)) {
                const Position r = unpack(rkey);
                if (A.accepts(r)) options[qi].push_back(rkey);
            }
            if (options[qi].empty()) throw std::runtime_error("opponent child has no P reply");
            for (uint64_t rkey : options[qi]) {
                if (carrier.count(rkey)) {
                    covered[qi] = 1;
                    --uncovered;
                    ++reused;
                    break;
                }
            }
        }

        if (!uncovered) return;

        std::unordered_map<uint64_t, uint32_t> frequency;
        frequency.reserve(uncovered * 8);
        for (size_t qi = 0; qi < qkeys.size(); ++qi) {
            if (covered[qi]) continue;
            for (uint64_t rkey : options[qi]) ++frequency[rkey];
        }

        std::vector<ReplyChoice> choices;
        choices.reserve(frequency.size());
        for (const auto& [key, count] : frequency)
            choices.push_back({key, count, area(unpack(key))});
        std::sort(choices.begin(), choices.end(), [&](const ReplyChoice& a, const ReplyChoice& b) {
            if (a.frequency != b.frequency) return a.frequency > b.frequency;
            if (a.area != b.area) return low_area ? a.area < b.area : a.area > b.area;
            return a.key < b.key;
        });

        uint64_t new_here = 0;
        for (const ReplyChoice& choice : choices) {
            if (!uncovered) break;
            bool useful = false;
            for (size_t qi = 0; qi < qkeys.size(); ++qi) {
                if (covered[qi]) continue;
                if (std::binary_search(options[qi].begin(), options[qi].end(), choice.key)) {
                    covered[qi] = 1;
                    --uncovered;
                    useful = true;
                }
            }
            if (useful) {
                const size_t before = carrier.size();
                insert_carrier(choice.key);
                if (carrier.size() != before) {
                    ++selected_new;
                    ++new_here;
                }
            }
        }
        if (uncovered) throw std::runtime_error("greedy cover failed despite nonempty replies");
        max_new_per_position = std::max(max_new_per_position, new_here);
    }
};

int main(int argc, char** argv) {
    try {
        if (argc < 2 || argc > 4) {
            std::cerr << "usage: " << argv[0] << " P.mdd [NODE_LIMIT] [low|high]\n";
            return 2;
        }
        const uint64_t limit = argc >= 3 ? std::stoull(argv[2]) : 2000000ULL;
        const std::string heuristic = argc >= 4 ? argv[3] : "low";
        if (heuristic != "low" && heuristic != "high")
            throw std::runtime_error("heuristic must be low or high");
        MDD mdd(argv[1]);
        Synthesizer synth(mdd, limit, heuristic == "low");
        return synth.run();
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return std::string(e.what()) == "carrier node limit exceeded" ? 3 : 1;
    }
}
