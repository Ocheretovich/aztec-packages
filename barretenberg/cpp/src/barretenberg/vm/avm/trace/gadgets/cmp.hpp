
#pragma once

#include "barretenberg/vm/avm/generated/relations/cmp.hpp"
#include "barretenberg/vm/avm/trace/common.hpp"
#include "barretenberg/vm/avm/trace/gadgets/range_check.hpp"
#include <cstdint>

enum class CmpOp { EQ, GT };

namespace bb::avm_trace {
class AvmCmpBuilder {
  public:
    struct CmpEvent {
        uint64_t clk;
        FF input_a;
        FF input_b;
        EventEmitter emitter;
        CmpOp op;
    };

    struct CmpEntry {
        uint64_t clk;
        FF input_a;
        FF input_b;
        FF result;
        FF op_eq_diff_inv;
        bool is_gt;
        bool is_eq;
        std::tuple<FF, FF> a_limbs;
        std::tuple<FF, FF> b_limbs;
        // Tuple of lo, hi and borrow
        std::tuple<FF, FF, FF> p_sub_a_limbs;
        std::tuple<FF, FF, FF> p_sub_b_limbs;
        std::tuple<FF, FF, FF> gt_result_limbs;
    };

    AvmRangeCheckBuilder range_check_builder;

    bool constrained_eq(FF a, FF b, uint64_t clk, EventEmitter e)
    {
        cmp_events.push_back({ clk, a, b, e, CmpOp::EQ });
        return uint256_t(a) == uint256_t(b);
    }
    // Constrains a > b
    bool constrained_gt(FF a, FF b, uint64_t clk, EventEmitter e)
    {
        cmp_events.push_back({ clk, a, b, e, CmpOp::GT });
        return uint256_t(a) > uint256_t(b);
    }

    // Turns cmp events into real entries
    std::vector<CmpEntry> finalize()
    {
        std::vector<CmpEntry> entries;
        // Process each range check event into entries
        for (auto& event : cmp_events) {
            auto entry = CmpEntry{};
            entry.clk = event.clk;
            entry.input_a = event.input_a;
            entry.input_b = event.input_b;
            auto input_a_u256 = uint256_t(event.input_a);
            auto input_b_u256 = uint256_t(event.input_b);

            if (CmpOp::EQ == event.op) {
                FF diff = event.input_a - event.input_b;
                entry.result = diff == FF::zero() ? FF::one() : FF::zero();
                entry.op_eq_diff_inv = diff == FF::zero() ? FF::zero() : diff.invert();
                entry.is_eq = true;
            } else {
                entry.result = input_a_u256 > input_b_u256;
                auto range_chk_clk = (entry.clk * (uint64_t(1) << 8)) + 5;
                // Set the limbs
                entry.a_limbs = decompose(input_a_u256, 128);
                // We can combine these steps
                range_check_builder.assert_range(std::get<0>(entry.a_limbs), 128, EventEmitter::CMP_LO, range_chk_clk);
                range_check_builder.assert_range(std::get<1>(entry.a_limbs), 128, EventEmitter::CMP_HI, range_chk_clk);

                entry.b_limbs = decompose(input_b_u256, 128);
                // We can combine these steps
                range_check_builder.assert_range(
                    std::get<0>(entry.b_limbs), 128, EventEmitter::CMP_LO, range_chk_clk - 1);
                range_check_builder.assert_range(
                    std::get<1>(entry.b_limbs), 128, EventEmitter::CMP_HI, range_chk_clk - 1);

                auto [p_sub_a_lo, p_sub_a_hi, p_a_borrow] = gt_witness(FF::modulus, input_a_u256);
                // We can combine these steps
                range_check_builder.assert_range(p_sub_a_lo, 128, EventEmitter::CMP_LO, range_chk_clk - 2);
                range_check_builder.assert_range(p_sub_a_hi, 128, EventEmitter::CMP_HI, range_chk_clk - 2);
                entry.p_sub_a_limbs = std::make_tuple(p_sub_a_lo, p_sub_a_hi, p_a_borrow);

                auto [p_sub_b_lo, p_sub_b_hi, p_b_borrow] = gt_witness(FF::modulus, input_b_u256);
                range_check_builder.assert_range(p_sub_b_lo, 128, EventEmitter::CMP_LO, range_chk_clk - 3);
                range_check_builder.assert_range(p_sub_a_hi, 128, EventEmitter::CMP_HI, range_chk_clk - 3);
                entry.p_sub_b_limbs = std::make_tuple(p_sub_b_lo, p_sub_b_hi, p_b_borrow);

                auto [r_lo, r_hi, borrow] = gt_or_lte_witness(input_a_u256, input_b_u256);
                range_check_builder.assert_range(r_lo, 128, EventEmitter::CMP_LO, range_chk_clk - 4);
                range_check_builder.assert_range(r_hi, 128, EventEmitter::CMP_HI, range_chk_clk - 4);
                entry.gt_result_limbs = std::make_tuple(r_lo, r_hi, borrow);
                entry.is_gt = true;
            }

            entries.push_back(entry);
        }
        return entries;
    }

    template <typename DestRow> void merge_into(std::array<DestRow, 5>& rows, CmpEntry const& entry)
    {
        auto& row = rows[0];
        row.cmp_clk = entry.clk;
        row.cmp_result = entry.result;
        row.cmp_op_eq_diff_inv = entry.op_eq_diff_inv;
        row.cmp_op_gt = entry.is_gt;
        row.cmp_op_eq = entry.is_eq;

        row.cmp_a_lo = std::get<0>(entry.a_limbs);
        row.cmp_a_hi = std::get<1>(entry.a_limbs);
        row.cmp_b_lo = std::get<0>(entry.b_limbs);
        row.cmp_b_hi = std::get<1>(entry.b_limbs);

        row.cmp_p_sub_a_lo = std::get<0>(entry.p_sub_a_limbs);
        row.cmp_p_sub_a_hi = std::get<1>(entry.p_sub_a_limbs);
        row.cmp_p_a_borrow = std::get<2>(entry.p_sub_a_limbs);

        row.cmp_p_sub_b_lo = std::get<0>(entry.p_sub_b_limbs);
        row.cmp_p_sub_b_hi = std::get<1>(entry.p_sub_b_limbs);
        row.cmp_p_b_borrow = std::get<2>(entry.p_sub_b_limbs);

        row.cmp_res_lo = std::get<0>(entry.gt_result_limbs);
        row.cmp_res_hi = std::get<1>(entry.gt_result_limbs);
        row.cmp_borrow = std::get<2>(entry.gt_result_limbs);

        row.cmp_input_a = entry.input_a;
        row.cmp_input_b = entry.input_b;
        row.cmp_result = entry.result;
        row.cmp_sel_cmp = FF::one();

        if (entry.is_gt) {
            row.cmp_cmp_rng_ctr = FF(5);
            row.cmp_range_chk_clk = row.cmp_clk * (uint64_t(1) << 8) + row.cmp_cmp_rng_ctr;
            row.cmp_sel_rng_chk = FF::one();
            row.cmp_op_eq_diff_inv = row.cmp_cmp_rng_ctr.invert();
            std::vector<FF> hi_lo_limbs{ std::get<0>(entry.b_limbs),         std::get<1>(entry.b_limbs),
                                         std::get<0>(entry.p_sub_a_limbs),   std::get<1>(entry.p_sub_a_limbs),
                                         std::get<0>(entry.p_sub_b_limbs),   std::get<1>(entry.p_sub_b_limbs),
                                         std::get<0>(entry.gt_result_limbs), std::get<1>(entry.gt_result_limbs) };
            for (size_t i = 0; i < 5; i++) {
                auto& row = rows[i + 1];
                // row.cmp_clk = entry.clk;
                row.cmp_sel_rng_chk = FF::one(); // i != 4 ? FF::one(): FF::zero();
                row.cmp_cmp_rng_ctr = FF(4 - i);
                row.cmp_range_chk_clk = rows[0].cmp_clk * (uint64_t(1) << 8) + row.cmp_cmp_rng_ctr;
                row.cmp_op_eq_diff_inv = i != 4 ? row.cmp_cmp_rng_ctr.invert() : FF::zero();
                row.cmp_a_lo = 2 * i < hi_lo_limbs.size() ? hi_lo_limbs[2 * i] : FF::zero();
                row.cmp_a_hi = 2 * i + 1 < hi_lo_limbs.size() ? hi_lo_limbs[2 * i + 1] : FF::zero();
                row.cmp_b_lo = 2 * i + 2 < hi_lo_limbs.size() ? hi_lo_limbs[2 * i + 2] : FF::zero();
                row.cmp_b_hi = 2 * i + 3 < hi_lo_limbs.size() ? hi_lo_limbs[2 * i + 3] : FF::zero();
                row.cmp_p_sub_a_lo = 2 * i + 4 < hi_lo_limbs.size() ? hi_lo_limbs[2 * i + 4] : FF::zero();
                row.cmp_p_sub_a_hi = 2 * i + 5 < hi_lo_limbs.size() ? hi_lo_limbs[2 * i + 5] : FF::zero();
                row.cmp_p_sub_b_lo = 2 * i + 6 < hi_lo_limbs.size() ? hi_lo_limbs[2 * i + 6] : FF::zero();
                row.cmp_p_sub_b_hi = 2 * i + 7 < hi_lo_limbs.size() ? hi_lo_limbs[2 * i + 7] : FF::zero();
            }
        }
    }

  private:
    std::vector<CmpEvent> cmp_events;
    std::tuple<uint256_t, uint256_t> decompose(uint256_t const& a, uint8_t const b)
    {
        uint256_t upper_bitmask = (uint256_t(1) << uint256_t(b)) - 1;
        uint256_t a_lo = a & upper_bitmask;
        uint256_t a_hi = a >> b;
        return std::make_tuple(a_lo, a_hi);
    }
    std::tuple<uint256_t, uint256_t, bool> gt_witness(uint256_t const& a, uint256_t const& b)
    {
        uint256_t two_pow_128 = uint256_t(1) << uint256_t(128);
        auto [a_lo, a_hi] = decompose(a, 128);
        auto [b_lo, b_hi] = decompose(b, 128);
        bool borrow = a_lo <= b_lo;
        auto borrow_u256 = uint256_t(static_cast<uint64_t>(borrow));
        uint256_t r_lo = a_lo - b_lo - 1 + borrow_u256 * two_pow_128;
        uint256_t r_hi = a_hi - b_hi - borrow_u256;
        return std::make_tuple(r_lo, r_hi, borrow);
    }
    std::tuple<uint256_t, uint256_t, bool> gt_or_lte_witness(uint256_t const& a, uint256_t const& b)
    {
        uint256_t two_pow_126 = uint256_t(1) << uint256_t(128);
        auto [a_lo, a_hi] = decompose(a, 128);
        auto [b_lo, b_hi] = decompose(b, 128);
        bool isGT = a > b;
        if (isGT) {
            return gt_witness(a, b);
        }
        bool borrow = b_lo < a_lo;
        auto borrow_u256 = uint256_t(static_cast<uint64_t>(borrow));
        uint256_t r_lo = b_lo - a_lo + borrow_u256 * two_pow_126;
        uint256_t r_hi = b_hi - a_hi - borrow_u256;
        return std::make_tuple(r_lo, r_hi, borrow);
    }
};
} // namespace bb::avm_trace
