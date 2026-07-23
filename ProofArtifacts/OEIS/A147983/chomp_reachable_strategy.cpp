// Extract a closed second-player strategy reachable from the three 10x42 Chomp roots.
//
// The exact P-rank database is discovery input only. For each opponent position reached from a
// carrier P-position, this program records one explicit legal P reply. The output is intended for
// a separately checked Lean certificate; this program itself is not trusted.

#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using State = std::array<uint8_t, 10>;

struct Database {
    int K = 0;
    int N = 0;
    std::vector<std::vector<uint64_t>> choose;
    std::vector<uint64_t> pRanks;

    explicit Database(const std::string& path) {
        std::ifstream in(path, std::ios::binary);
        if (!in) throw std::runtime_error("cannot open rank database");
        char magic[8];
        uint64_t k = 0, n = 0;
        in.read(magic, 8);
        in.read(reinterpret_cast<char*>(&k), 8);
        in.read(reinterpret_cast<char*>(&n), 8);
        if (!in || std::string(magic, 8) != "CHPRANK1" || k != 10 || n != 42)
            throw std::runtime_error("unexpected rank database");
        K = static_cast<int>(k);
        N = static_cast<int>(n);
        in.seekg(0, std::ios::end);
        const uint64_t size = static_cast<uint64_t>(in.tellg());
        if (size < 24 || (size - 24) % 8) throw std::runtime_error("bad database size");
        pRanks.resize((size - 24) / 8);
        in.seekg(24, std::ios::beg);
        in.read(reinterpret_cast<char*>(pRanks.data()),
                static_cast<std::streamsize>(pRanks.size() * sizeof(uint64_t)));
        if (!in || !std::is_sorted(pRanks.begin(), pRanks.end()))
            throw std::runtime_error("unsorted P-rank database");

        choose.assign(N + K + 3, std::vector<uint64_t>(K + 3));
        for (int a = 0; a < static_cast<int>(choose.size()); ++a) {
            choose[a][0] = 1;
            for (int b = 1; b <= std::min(a, K + 1); ++b) {
                __uint128_t z = static_cast<__uint128_t>(choose[a - 1][b - 1]) +
                                choose[a - 1][b];
                if (z > std::numeric_limits<uint64_t>::max())
                    throw std::runtime_error("rank overflow");
                choose[a][b] = static_cast<uint64_t>(z);
            }
        }
    }

    uint64_t rank(const State& s) const {
        uint64_t r = 0;
        for (int pos = 0; pos < K; ++pos) {
            const int j = K - pos;
            r += choose[static_cast<int>(s[pos]) + j - 1][j];
        }
        return r;
    }

    bool isP(const State& s) const {
        return std::binary_search(pRanks.begin(), pRanks.end(), rank(s));
    }
};

static uint64_t pack(const State& s) {
    uint64_t z = 0;
    for (int i = 0; i < 10; ++i) z |= static_cast<uint64_t>(s[i]) << (6 * i);
    return z;
}

static State unpack(uint64_t z) {
    State s{};
    for (int i = 0; i < 10; ++i) s[i] = static_cast<uint8_t>((z >> (6 * i)) & 63U);
    return s;
}

static std::string show(const State& s) {
    std::ostringstream out;
    out << '(';
    for (int i = 0; i < 10; ++i) {
        if (i) out << ',';
        out << static_cast<int>(s[i]);
    }
    out << ')';
    return out.str();
}

static std::vector<State> children(const State& p) {
    std::vector<State> out;
    out.reserve(420);
    for (int row = 0; row < 10; ++row) {
        for (int target = 0; target < p[row]; ++target) {
            if (row == 0 && target == 0) continue;
            State q = p;
            for (int j = row; j < 10; ++j)
                q[j] = static_cast<uint8_t>(std::min<int>(q[j], target));
            out.push_back(q);
        }
    }
    std::sort(out.begin(), out.end(), [](const State& a, const State& b) {
        return pack(a) < pack(b);
    });
    out.erase(std::unique(out.begin(), out.end(), [](const State& a, const State& b) {
        return pack(a) == pack(b);
    }), out.end());
    return out;
}

static void write_u64(std::ofstream& out, uint64_t x) {
    out.write(reinterpret_cast<const char*>(&x), sizeof(x));
}

int main(int argc, char** argv) {
    try {
        if (argc != 5) {
            std::cerr << "usage: " << argv[0]
                      << " P_RANKS.bin P_LIMIT CARRIER.bin RESPONSES.bin\n";
            return 2;
        }
        Database db(argv[1]);
        const uint64_t limit = std::stoull(argv[2]);

        const std::array<State, 3> roots = {{
            {{42,42,42,42,35,35,35,35,35,35}},
            {{42,42,42,42,42,42,29,29,29,29}},
            {{42,42,42,42,42,42,42,25,25,25}}
        }};

        std::unordered_set<uint64_t> carrier;
        std::unordered_map<uint64_t, uint64_t> response;
        std::vector<uint64_t> stack;
        carrier.reserve(static_cast<size_t>(std::min<uint64_t>(limit * 2, 30000000)));
        response.reserve(static_cast<size_t>(std::min<uint64_t>(limit * 20, 100000000)));

        for (const State& root : roots) {
            if (!db.isP(root)) throw std::runtime_error("root is not P: " + show(root));
            const uint64_t key = pack(root);
            if (carrier.insert(key).second) stack.push_back(key);
        }

        uint64_t processedP = 0;
        uint64_t opponentEdges = 0;
        uint64_t reusedResponses = 0;
        bool complete = true;

        while (!stack.empty()) {
            const uint64_t pkey = stack.back();
            stack.pop_back();
            const State p = unpack(pkey);
            if (!db.isP(p)) throw std::runtime_error("carrier contains non-P state");
            ++processedP;

            for (const State& q : children(p)) {
                ++opponentEdges;
                if (db.isP(q))
                    throw std::runtime_error("P state has P child: " + show(p) + " -> " + show(q));
                const uint64_t qkey = pack(q);
                uint64_t rkey = 0;
                auto cached = response.find(qkey);
                if (cached != response.end()) {
                    rkey = cached->second;
                    ++reusedResponses;
                } else {
                    bool found = false;
                    uint64_t bestRank = std::numeric_limits<uint64_t>::max();
                    for (const State& r : children(q)) {
                        if (!db.isP(r)) continue;
                        const uint64_t candidate = pack(r);
                        if (carrier.count(candidate)) {
                            rkey = candidate;
                            found = true;
                            break;
                        }
                        const uint64_t rr = db.rank(r);
                        if (!found || rr < bestRank || (rr == bestRank && candidate < rkey)) {
                            found = true;
                            bestRank = rr;
                            rkey = candidate;
                        }
                    }
                    if (!found)
                        throw std::runtime_error("opponent state has no P reply: " + show(q));
                    response.emplace(qkey, rkey);
                }

                State r = unpack(rkey);
                if (!db.isP(r)) throw std::runtime_error("recorded response is not P");
                if (carrier.insert(rkey).second) {
                    if (carrier.size() > limit) {
                        complete = false;
                        stack.clear();
                        break;
                    }
                    stack.push_back(rkey);
                }
            }

            if (processedP % 10000 == 0) {
                std::cerr << "processedP=" << processedP
                          << " carrier=" << carrier.size()
                          << " responses=" << response.size()
                          << " edges=" << opponentEdges
                          << " stack=" << stack.size() << '\n';
            }
            if (!complete) break;
        }

        std::vector<uint64_t> carrierRanks;
        carrierRanks.reserve(carrier.size());
        for (uint64_t key : carrier) carrierRanks.push_back(db.rank(unpack(key)));
        std::sort(carrierRanks.begin(), carrierRanks.end());

        std::vector<std::pair<uint64_t,uint64_t>> responses(response.begin(), response.end());
        std::sort(responses.begin(), responses.end());

        std::ofstream carrierOut(argv[3], std::ios::binary);
        if (!carrierOut) throw std::runtime_error("cannot create carrier output");
        carrierOut.write("CHCARR01", 8);
        write_u64(carrierOut, carrierRanks.size());
        for (uint64_t r : carrierRanks) write_u64(carrierOut, r);

        std::ofstream responseOut(argv[4], std::ios::binary);
        if (!responseOut) throw std::runtime_error("cannot create response output");
        responseOut.write("CHRESP01", 8);
        write_u64(responseOut, responses.size());
        for (const auto& [q, r] : responses) {
            write_u64(responseOut, q);
            write_u64(responseOut, r);
        }

        std::cout << (complete ? "COMPLETE" : "LIMIT")
                  << " processedP=" << processedP
                  << " carrier=" << carrier.size()
                  << " responses=" << response.size()
                  << " opponentEdges=" << opponentEdges
                  << " reusedResponses=" << reusedResponses
                  << " pending=" << stack.size() << '\n';
        return complete ? 0 : 3;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return 1;
    }
}