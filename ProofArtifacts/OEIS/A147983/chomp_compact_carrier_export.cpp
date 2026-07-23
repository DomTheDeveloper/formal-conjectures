// Synthesize and export a compact closed two-ply response carrier for the three 10x42 roots.
//
// The P-position MDD is an untrusted discovery oracle. The exported carrier and reply table must
// subsequently be translated into explicit Lean proof terms and checked by the kernel.

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
        uint32_t low = n.offset, high = n.offset + n.length;
        while (low < high) {
            const uint32_t middle = low + (high - low) / 2;
            const uint32_t packed = layer[depth].transitions[middle];
            const uint8_t stored = static_cast<uint8_t>(packed & 63U);
            if (stored < symbol) low = middle + 1; else high = middle;
        }
        if (low == n.offset + n.length) return -1;
        const uint32_t packed = layer[depth].transitions[low];
        if ((packed & 63U) != symbol) return -1;
        return static_cast<int32_t>(packed >> 6);
    }

    bool accepts(const Position& position) const {
        uint32_t node = root;
        for (int depth = 0; depth < 10; ++depth) {
            const int32_t next = step(depth, node, position[depth]);
            if (next < 0) return false;
            node = static_cast<uint32_t>(next);
        }
        return true;
    }
};

static uint64_t pack(const Position& position) {
    uint64_t value = 0;
    for (int i = 0; i < 10; ++i)
        value |= static_cast<uint64_t>(position[i]) << (6 * i);
    return value;
}

static Position unpack(uint64_t value) {
    Position position{};
    for (int i = 0; i < 10; ++i)
        position[i] = static_cast<uint8_t>((value >> (6 * i)) & 63U);
    return position;
}

static int area(const Position& position) {
    int result = 0;
    for (uint8_t row : position) result += row;
    return result;
}

static std::vector<uint64_t> children(const Position& position) {
    std::vector<uint64_t> result;
    result.reserve(420);
    for (int row = 0; row < 10; ++row) {
        const int lower = row == 0 ? 1 : 0;
        for (int target = lower; target < position[row]; ++target) {
            Position child = position;
            for (int j = row; j < 10; ++j)
                child[j] = static_cast<uint8_t>(std::min<int>(child[j], target));
            result.push_back(pack(child));
        }
    }
    std::sort(result.begin(), result.end());
    result.erase(std::unique(result.begin(), result.end()), result.end());
    return result;
}

static bool isChild(uint64_t parent, uint64_t child) {
    const std::vector<uint64_t> options = children(unpack(parent));
    return std::binary_search(options.begin(), options.end(), child);
}

struct ReplyChoice {
    uint64_t key;
    uint32_t frequency;
    int area;
};

static void writeU64(std::ofstream& output, uint64_t value) {
    output.write(reinterpret_cast<const char*>(&value), sizeof(value));
}

class Synthesizer {
public:
    Synthesizer(const MDD& mdd, uint64_t limit)
        : A(mdd), nodeLimit(limit) {}

    void run(const std::string& carrierPath, const std::string& responsePath) {
        const std::array<Position, 3> roots = {{
            {{42,42,42,42,35,35,35,35,35,35}},
            {{42,42,42,42,42,42,29,29,29,29}},
            {{42,42,42,42,42,42,42,25,25,25}}
        }};
        for (const Position& root : roots) {
            if (!A.accepts(root)) throw std::runtime_error("target root absent from P MDD");
            insertCarrier(pack(root));
        }

        while (!stack.empty()) {
            const uint64_t parent = stack.back();
            stack.pop_back();
            processPosition(parent);
            ++processed;
            if (processed % 10000 == 0) {
                std::cerr << "processed=" << processed
                          << " carrier=" << carrier.size()
                          << " responses=" << response.size()
                          << " stack=" << stack.size()
                          << " max_new=" << maxNewPerPosition << '\n';
            }
        }

        verifyClosed();
        writeOutputs(carrierPath, responsePath);
        std::cout << "COMPLETE carrier=" << carrier.size()
                  << " processed=" << processed
                  << " responses=" << response.size()
                  << " selected_new=" << selectedNew
                  << " reused=" << reused
                  << " max_opponent_children=" << maxOpponentChildren
                  << " max_new_per_position=" << maxNewPerPosition
                  << " heuristic=high-area\n";
    }

private:
    const MDD& A;
    uint64_t nodeLimit;
    std::unordered_set<uint64_t> carrier;
    std::unordered_map<uint64_t, uint64_t> response;
    std::vector<uint64_t> stack;
    uint64_t processed = 0;
    uint64_t selectedNew = 0;
    uint64_t reused = 0;
    uint64_t maxOpponentChildren = 0;
    uint64_t maxNewPerPosition = 0;

    void insertCarrier(uint64_t key) {
        if (!A.accepts(unpack(key))) throw std::runtime_error("attempted to add non-P carrier node");
        if (carrier.insert(key).second) {
            if (carrier.size() > nodeLimit)
                throw std::runtime_error("carrier node limit exceeded");
            stack.push_back(key);
        }
    }

    void processPosition(uint64_t parentKey) {
        const std::vector<uint64_t> opponents = children(unpack(parentKey));
        maxOpponentChildren = std::max<uint64_t>(maxOpponentChildren, opponents.size());

        std::vector<std::vector<uint64_t>> options(opponents.size());
        std::vector<uint8_t> covered(opponents.size(), 0);
        size_t uncovered = opponents.size();

        for (size_t index = 0; index < opponents.size(); ++index) {
            const uint64_t opponent = opponents[index];
            if (A.accepts(unpack(opponent)))
                throw std::runtime_error("carrier P-position has a P child");

            const auto recorded = response.find(opponent);
            if (recorded != response.end()) {
                if (!carrier.count(recorded->second) || !isChild(opponent, recorded->second))
                    throw std::runtime_error("recorded reply is invalid");
                covered[index] = 1;
                --uncovered;
                ++reused;
                continue;
            }

            for (uint64_t candidate : children(unpack(opponent))) {
                if (A.accepts(unpack(candidate))) options[index].push_back(candidate);
            }
            if (options[index].empty())
                throw std::runtime_error("opponent child has no P reply");

            for (uint64_t candidate : options[index]) {
                if (carrier.count(candidate)) {
                    response.emplace(opponent, candidate);
                    covered[index] = 1;
                    --uncovered;
                    ++reused;
                    break;
                }
            }
        }

        if (!uncovered) return;

        std::unordered_map<uint64_t, uint32_t> frequency;
        frequency.reserve(uncovered * 8);
        for (size_t index = 0; index < opponents.size(); ++index) {
            if (covered[index]) continue;
            for (uint64_t candidate : options[index]) ++frequency[candidate];
        }

        std::vector<ReplyChoice> choices;
        choices.reserve(frequency.size());
        for (const auto& [key, count] : frequency)
            choices.push_back({key, count, area(unpack(key))});
        std::sort(choices.begin(), choices.end(), [](const ReplyChoice& left,
                                                     const ReplyChoice& right) {
            if (left.frequency != right.frequency) return left.frequency > right.frequency;
            if (left.area != right.area) return left.area > right.area;
            return left.key < right.key;
        });

        uint64_t newHere = 0;
        for (const ReplyChoice& choice : choices) {
            if (!uncovered) break;
            bool useful = false;
            for (size_t index = 0; index < opponents.size(); ++index) {
                if (covered[index]) continue;
                if (std::binary_search(options[index].begin(), options[index].end(), choice.key)) {
                    response.emplace(opponents[index], choice.key);
                    covered[index] = 1;
                    --uncovered;
                    useful = true;
                }
            }
            if (useful) {
                const size_t before = carrier.size();
                insertCarrier(choice.key);
                if (carrier.size() != before) {
                    ++selectedNew;
                    ++newHere;
                }
            }
        }
        if (uncovered) throw std::runtime_error("greedy cover failed");
        maxNewPerPosition = std::max(maxNewPerPosition, newHere);
    }

    void verifyClosed() const {
        for (uint64_t parent : carrier) {
            for (uint64_t opponent : children(unpack(parent))) {
                const auto found = response.find(opponent);
                if (found == response.end())
                    throw std::runtime_error("missing reply during final closure verification");
                const uint64_t reply = found->second;
                if (!carrier.count(reply))
                    throw std::runtime_error("reply leaves carrier");
                if (!A.accepts(unpack(reply)))
                    throw std::runtime_error("reply is not P");
                if (!isChild(opponent, reply))
                    throw std::runtime_error("reply is not a legal move");
                if (area(unpack(reply)) >= area(unpack(parent)))
                    throw std::runtime_error("two-ply response does not decrease area");
            }
        }
    }

    void writeOutputs(const std::string& carrierPath,
                      const std::string& responsePath) const {
        std::vector<uint64_t> carrierKeys(carrier.begin(), carrier.end());
        std::sort(carrierKeys.begin(), carrierKeys.end(), [](uint64_t left, uint64_t right) {
            const int leftArea = area(unpack(left));
            const int rightArea = area(unpack(right));
            return leftArea != rightArea ? leftArea < rightArea : left < right;
        });
        std::vector<std::pair<uint64_t, uint64_t>> responses(response.begin(), response.end());
        std::sort(responses.begin(), responses.end());

        std::ofstream carrierOutput(carrierPath, std::ios::binary);
        if (!carrierOutput) throw std::runtime_error("cannot create carrier output");
        carrierOutput.write("CHCARR02", 8);
        writeU64(carrierOutput, carrierKeys.size());
        for (uint64_t key : carrierKeys) writeU64(carrierOutput, key);

        std::ofstream responseOutput(responsePath, std::ios::binary);
        if (!responseOutput) throw std::runtime_error("cannot create response output");
        responseOutput.write("CHRESP02", 8);
        writeU64(responseOutput, responses.size());
        for (const auto& [opponent, reply] : responses) {
            writeU64(responseOutput, opponent);
            writeU64(responseOutput, reply);
        }
    }
};

int main(int argc, char** argv) {
    try {
        if (argc != 5) {
            std::cerr << "usage: " << argv[0]
                      << " P.mdd NODE_LIMIT CARRIER.bin RESPONSES.bin\n";
            return 2;
        }
        MDD mdd(argv[1]);
        Synthesizer synthesizer(mdd, std::stoull(argv[2]));
        synthesizer.run(argv[3], argv[4]);
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "error: " << error.what() << '\n';
        return std::string(error.what()) == "carrier node limit exceeded" ? 3 : 1;
    }
}