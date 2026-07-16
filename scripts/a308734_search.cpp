// Copyright 2026 The Formal Conjectures Authors.
// Licensed under the Apache License, Version 2.0.
//
// Exhaustively checks the bounded-exponent variant of OEIS A308734:
//   n = (2^a 3^b)^2 + (2^c 5^d)^2 + x^2 + y^2,
// with b,d <= B and all other variables nonnegative.
//
// Build:
//   c++ -O3 -std=c++20 scripts/a308734_search.cpp -o /tmp/a308734_search
// Examples:
//   /tmp/a308734_search 1000000000 4
//   /tmp/a308734_search 1000000000 5

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

int main(int argc, char** argv) {
  const std::uint32_t limit = argc > 1 ? std::stoul(argv[1]) : 100000000;
  const int exponent_bound = argc > 2 ? std::stoi(argv[2]) : 4;

  if (limit < 2 || exponent_bound < 0) {
    std::cerr << "usage: a308734_search LIMIT NONNEGATIVE_EXPONENT_BOUND\n";
    return EXIT_FAILURE;
  }

  // sum_two_squares[m] is computed using Fermat's two-square criterion:
  // each prime p == 3 (mod 4) must occur to an even exponent in m.
  std::vector<std::uint8_t> is_prime(limit + 1, 1);
  std::vector<std::uint8_t> sum_two_squares(limit + 1, 1);
  is_prime[0] = is_prime[1] = 0;
  sum_two_squares[0] = 1;

  for (std::uint32_t i = 2; static_cast<std::uint64_t>(i) * i <= limit; ++i) {
    if (!is_prime[i]) continue;
    for (std::uint64_t j = static_cast<std::uint64_t>(i) * i; j <= limit; j += i) {
      is_prime[static_cast<std::size_t>(j)] = 0;
    }
  }

  std::size_t primes_three_mod_four = 0;
  for (std::uint32_t p = 3; p <= limit; p += 4) {
    if (!is_prime[p]) continue;
    ++primes_three_mod_four;
    std::uint64_t odd_power = p;
    while (odd_power <= limit) {
      const std::uint64_t next_power = odd_power * p;
      for (std::uint64_t m = odd_power; m <= limit; m += odd_power) {
        if (next_power > limit || m % next_power != 0) {
          sum_two_squares[static_cast<std::size_t>(m)] = 0;
        }
      }
      if (odd_power > limit / static_cast<std::uint64_t>(p) / p) break;
      odd_power *= static_cast<std::uint64_t>(p) * p;
    }
  }

  const std::uint64_t root_limit =
      static_cast<std::uint64_t>(std::sqrt(static_cast<long double>(limit)));
  std::vector<std::uint64_t> first_coordinates;
  std::vector<std::uint64_t> second_coordinates;

  for (std::uint64_t power_two = 1; power_two <= root_limit; power_two *= 2) {
    std::uint64_t power_three = 1;
    for (int b = 0; b <= exponent_bound; ++b, power_three *= 3) {
      if (power_two * power_three <= root_limit) {
        first_coordinates.push_back(power_two * power_three);
      }
    }
    if (power_two > root_limit / 2) break;
  }

  for (std::uint64_t power_two = 1; power_two <= root_limit; power_two *= 2) {
    std::uint64_t power_five = 1;
    for (int d = 0; d <= exponent_bound; ++d, power_five *= 5) {
      if (power_two * power_five <= root_limit) {
        second_coordinates.push_back(power_two * power_five);
      }
    }
    if (power_two > root_limit / 2) break;
  }

  auto sort_unique = [](auto& values) {
    std::sort(values.begin(), values.end());
    values.erase(std::unique(values.begin(), values.end()), values.end());
  };
  sort_unique(first_coordinates);
  sort_unique(second_coordinates);

  std::vector<std::uint32_t> shifts;
  for (const std::uint64_t u : first_coordinates) {
    for (const std::uint64_t v : second_coordinates) {
      const std::uint64_t shift = u * u + v * v;
      if (shift <= limit) shifts.push_back(static_cast<std::uint32_t>(shift));
    }
  }
  sort_unique(shifts);

  std::cerr << "limit=" << limit << " exponent_bound=" << exponent_bound
            << " primes_3_mod_4=" << primes_three_mod_four
            << " first_coordinates=" << first_coordinates.size()
            << " second_coordinates=" << second_coordinates.size()
            << " shifts=" << shifts.size() << '\n';

  std::uint64_t exceptions = 0;
  std::uint64_t checks = 0;
  std::uint64_t maximum_checks = 0;
  std::uint32_t hardest = 0;

  for (std::uint32_t n = 2; n <= limit; ++n) {
    bool represented = false;
    std::uint64_t local_checks = 0;
    for (const std::uint32_t shift : shifts) {
      if (shift > n) break;
      ++local_checks;
      if (sum_two_squares[n - shift]) {
        represented = true;
        break;
      }
    }
    checks += local_checks;
    if (local_checks > maximum_checks) {
      maximum_checks = local_checks;
      hardest = n;
    }
    if (!represented) {
      ++exceptions;
      std::cout << n << '\n';
    }
  }

  std::cerr << "exceptions=" << exceptions
            << " average_checks=" << static_cast<double>(checks) / (limit - 1)
            << " maximum_checks=" << maximum_checks
            << " hardest=" << hardest << '\n';
  return exceptions == 0 ? EXIT_SUCCESS : 2;
}
