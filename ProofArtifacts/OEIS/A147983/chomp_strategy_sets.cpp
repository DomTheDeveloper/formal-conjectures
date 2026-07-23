// Exact collision-safe symbolic response checker with hash-consed reply-candidate sets.
//
// For one fixed opponent move template, this traverses the exact P-position MDD.  The state is
// (depth, source MDD node, interned set of still-possible legal replies).  Candidate vectors are
// stored once, transitions between candidate sets are memoized, and every hash hit is checked by
// exact comparison.  A completed traversal proves that every legal instance of the selected first
// move from every P-position represented by the MDD has some legal reply back into the P-language.

#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
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
        for (int depth = 0; depth < 10; ++depth) {
            in.read(reinterpret_cast<char*>(&nodes[depth]), 8);
            in.read(reinterpret_cast<char*>(&transitions[depth]), 8);
        }
        for (int depth = 0; depth < 10; ++depth) {
            if (nodes[depth] > UINT32_MAX || transitions[depth] > UINT32_MAX)
                throw std::runtime_error("MDD layer too large");
            layer[depth].nodes.resize(nodes[depth]);
            layer[depth].transitions.resize(transitions[depth]);
            for (Node& node : layer[depth].nodes) {
                in.read(reinterpret_cast<char*>(&node.offset), 4);
                in.read(reinterpret_cast<char*>(&node.length), 4);
                if (static_cast<uint64_t>(node.offset) + node.length > transitions[depth])
                    throw std::runtime_error("bad node span");
            }
            in.read(reinterpret_cast<char*>(layer[depth].transitions.data()),
                    static_cast<std::streamsize>(transitions[depth] * sizeof(uint32_t)));
        }
        if (!in) throw std::runtime_error("truncated MDD");
        if (root >= layer[0].nodes.size()) throw std::runtime_error("bad root");
    }

    int32_t step(int depth, uint32_t node, uint8_t symbol) const {
        const Node& current = layer[depth].nodes.at(node);
        uint32_t low = current.offset, high = current.offset + current.length;
        while (low < high) {
            const uint32_t middle = low + (high - low) / 2;
            const uint32_t packed = layer[depth].transitions[middle];
            if ((packed & 63U) < symbol) low = middle + 1; else high = middle;
        }
        if (low == current.offset + current.length) return -1;
        const uint32_t packed = layer[depth].transitions[low];
        if ((packed & 63U) != symbol) return -1;
        return static_cast<int32_t>(packed >> 6);
    }
};

struct Candidate {
    // row = 255 means the bite row has already been processed.
    uint8_t row, target;
    uint32_t node;
    bool operator==(const Candidate& other) const {
        return row == other.row && target == other.target && node == other.node;
    }
    bool operator<(const Candidate& other) const {
        if (row != other.row) return row < other.row;
        if (target != other.target) return target < other.target;
        return node < other.node;
    }
};

static uint64_t mix(uint64_t value) {
    value ^= value >> 30; value *= 0xbf58476d1ce4e5b9ULL;
    value ^= value >> 27; value *= 0x94d049bb133111ebULL;
    value ^= value >> 31; return value;
}

static uint64_t candidate_hash(const std::vector<Candidate>& values) {
    uint64_t hash = mix(values.size());
    for (const Candidate& candidate : values) {
        const uint64_t packed = (static_cast<uint64_t>(candidate.row) << 40) |
                                (static_cast<uint64_t>(candidate.target) << 32) |
                                candidate.node;
        hash = mix(hash ^ mix(packed + 0x9e3779b97f4a7c15ULL));
    }
    return hash;
}

class CandidatePool {
public:
    uint32_t intern(std::vector<Candidate> values) {
        std::sort(values.begin(), values.end());
        values.erase(std::unique(values.begin(), values.end()), values.end());
        const uint64_t hash = candidate_hash(values);
        auto found = buckets.find(hash);
        if (found != buckets.end()) {
            for (uint32_t identifier : found->second)
                if (sets[identifier] == values) return identifier;
        }
        if (sets.size() >= UINT32_MAX) throw std::runtime_error("too many candidate sets");
        const uint32_t identifier = static_cast<uint32_t>(sets.size());
        sets.push_back(std::move(values));
        buckets[hash].push_back(identifier);
        return identifier;
    }

    const std::vector<Candidate>& get(uint32_t identifier) const { return sets.at(identifier); }
    size_t size() const { return sets.size(); }
    uint64_t entries() const {
        uint64_t result = 0;
        for (const auto& set : sets) result += set.size();
        return result;
    }

    void print() const {
        for (uint32_t identifier = 0; identifier < sets.size(); ++identifier) {
            std::cout << "set=" << identifier << " size=" << sets[identifier].size();
            if (sets[identifier].size() <= 64) {
                std::cout << " candidates=";
                for (const Candidate& candidate : sets[identifier])
                    std::cout << '(' << static_cast<int>(candidate.row) << ','
                              << static_cast<int>(candidate.target) << ',' << candidate.node << ')';
            }
            std::cout << '\n';
        }
    }

private:
    std::vector<std::vector<Candidate>> sets;
    std::unordered_map<uint64_t, std::vector<uint32_t>> buckets;
};

class Checker {
public:
    Checker(const MDD& mdd, int first_row, int first_target, uint64_t state_limit)
        : A(mdd), firstRow(first_row), firstTarget(first_target), stateLimit(state_limit) {
        std::vector<Candidate> initial;
        for (int row = 0; row < 10; ++row) {
            const int low = row == 0 ? 1 : 0;
            for (int target = low; target < 42; ++target)
                initial.push_back({static_cast<uint8_t>(row), static_cast<uint8_t>(target), A.root});
        }
        initialSet = pool.intern(std::move(initial));
    }

    bool run() {
        prefix.fill(0);
        const bool result = visit(0, A.root, initialSet);
        std::cout << "RESULT first=" << firstRow << ',' << firstTarget
                  << " closed=" << (result ? 1 : 0)
                  << " states=" << memo.size()
                  << " calls=" << calls
                  << " hits=" << hits
                  << " sets=" << pool.size()
                  << " entries=" << pool.entries()
                  << " advance_cache=" << advanceCache.size() << '\n';
        pool.print();
        if (!result) {
            std::cout << "counterexample=";
            for (int depth = 0; depth < 10; ++depth) {
                if (depth) std::cout << ',';
                std::cout << static_cast<int>(counterexample[depth]);
            }
            std::cout << '\n';
        }
        return result;
    }

private:
    const MDD& A;
    int firstRow, firstTarget;
    uint64_t stateLimit;
    CandidatePool pool;
    uint32_t initialSet = 0;
    std::unordered_set<uint64_t> memo;
    std::unordered_map<uint64_t, uint32_t> advanceCache;
    std::array<uint8_t, 10> prefix{}, counterexample{};
    uint64_t calls = 0, hits = 0;

    uint64_t state_key(int depth, uint32_t source, uint32_t set) const {
        if (source >= (1U << 27)) throw std::runtime_error("source node does not fit state key");
        return (static_cast<uint64_t>(depth) << 59) |
               (static_cast<uint64_t>(source) << 32) | set;
    }

    uint32_t advance(int depth, uint8_t qsymbol, uint32_t setIdentifier) {
        const uint64_t key = (static_cast<uint64_t>(depth) << 56) |
                             (static_cast<uint64_t>(setIdentifier) << 8) | qsymbol;
        auto cached = advanceCache.find(key);
        if (cached != advanceCache.end()) return cached->second;

        std::vector<Candidate> output;
        output.reserve(pool.get(setIdentifier).size());
        for (Candidate candidate : pool.get(setIdentifier)) {
            uint8_t resultSymbol = qsymbol;
            if (candidate.row == 255) {
                resultSymbol = std::min<uint8_t>(qsymbol, candidate.target);
            } else if (depth < candidate.row) {
                resultSymbol = qsymbol;
            } else if (depth == candidate.row) {
                if (qsymbol <= candidate.target) continue;
                resultSymbol = candidate.target;
                candidate.row = 255;
            } else {
                throw std::runtime_error("uncanonicalized reply phase");
            }
            const int32_t next = A.step(depth, candidate.node, resultSymbol);
            if (next < 0) continue;
            candidate.node = static_cast<uint32_t>(next);
            output.push_back(candidate);
        }
        const uint32_t result = output.empty() ? UINT32_MAX : pool.intern(std::move(output));
        advanceCache.emplace(key, result);
        return result;
    }

    void complete_source(int depth, uint32_t node, std::array<uint8_t, 10>& word) const {
        for (int current = depth; current < 10; ++current) {
            const Node& source = A.layer[current].nodes.at(node);
            if (!source.length) throw std::runtime_error("dead source node");
            const uint32_t packed = A.layer[current].transitions[source.offset];
            word[current] = static_cast<uint8_t>(packed & 63U);
            node = packed >> 6;
        }
    }

    bool visit(int depth, uint32_t source, uint32_t setIdentifier) {
        ++calls;
        if (setIdentifier == UINT32_MAX) {
            counterexample = prefix;
            complete_source(depth, source, counterexample);
            return false;
        }
        if (depth == 10) return true;
        const uint64_t key = state_key(depth, source, setIdentifier);
        if (memo.find(key) != memo.end()) { ++hits; return true; }
        if (memo.size() >= stateLimit) throw std::runtime_error("strategy state limit exceeded");

        const Node& sourceNode = A.layer[depth].nodes.at(source);
        for (uint32_t index = 0; index < sourceNode.length; ++index) {
            const uint32_t packed = A.layer[depth].transitions[sourceNode.offset + index];
            const uint8_t psymbol = static_cast<uint8_t>(packed & 63U);
            const uint32_t sourceNext = packed >> 6;
            if (depth == firstRow && psymbol <= firstTarget) continue;
            const uint8_t qsymbol = depth < firstRow
                ? psymbol : std::min<uint8_t>(psymbol, static_cast<uint8_t>(firstTarget));
            prefix[depth] = psymbol;
            const uint32_t childSet = advance(depth, qsymbol, setIdentifier);
            if (!visit(depth + 1, sourceNext, childSet)) return false;
        }
        memo.insert(key);
        return true;
    }
};

int main(int argc, char** argv) {
    try {
        if (argc < 4 || argc > 5) {
            std::cerr << "usage: " << argv[0] << " P.mdd FIRST_ROW FIRST_TARGET [STATE_LIMIT]\n";
            return 2;
        }
        const int row = std::stoi(argv[2]);
        const int target = std::stoi(argv[3]);
        if (row < 0 || row >= 10 || target < (row == 0 ? 1 : 0) || target >= 42)
            throw std::runtime_error("invalid first move template");
        const uint64_t limit = argc == 5 ? std::stoull(argv[4]) : 30000000ULL;
        MDD mdd(argv[1]);
        Checker checker(mdd, row, target, limit);
        return checker.run() ? 0 : 1;
    } catch (const std::exception& error) {
        std::cerr << "error: " << error.what() << '\n';
        return 3;
    }
}
