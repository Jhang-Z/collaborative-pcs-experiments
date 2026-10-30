#pragma once
#include <cstddef>
#include <limits>
#include <stdexcept>

namespace pa {
// The pinned author's FFT/next_pow2 paths use signed-int shifts. Keep every
// power-of-two size below the sign bit; this is not an experiment-size cap.
constexpr size_t native_index_limit = size_t(1) << (std::numeric_limits<int>::digits - 1);
inline void validate_parties(size_t n) {
    if (n < 4 || (n & (n - 1)) || n > native_index_limit / 2)
        throw std::runtime_error("parties must be a power of two >=4 with 2*N in the native FFT range");
}
inline size_t keccak_table_length(size_t instances, size_t padded) {
    if (!instances || (instances & (instances - 1)) || !padded || (padded & (padded - 1))
        || instances > native_index_limit / padded)
        throw std::runtime_error("Keccak batch must be a power of two within the native table index range");
    return instances * padded;
}
inline size_t pcs_row_length(size_t n, size_t m, size_t padding) {
    validate_parties(n);
    if (m < 8 || (m & (m - 1)) || m < n / 4)
        throw std::runtime_error("PCS bits must be a power of two >=8 and contain at least N/4 entries");
    if (padding > native_index_limit / 4 || m / (n / 4) > native_index_limit / 4 - padding)
        throw std::runtime_error("encoded PCS row exceeds the native FFT index range");
    size_t d = 1;
    while (d < m / (n / 4) + padding) d <<= 1;
    return d;
}
}
