// SPDX-License-Identifier: GPL-2.0-only
/* tnum: tracked (or tristate) numbers
 *
 * Cherry-picked portions for trirocq verification.
 * Value-mask computation split because VST cannot handle struct copying.
 *
 * Error message from VST:
 *     "contains internal structure-copying, a feature of C not
 *     currently supported in Verifiable C (level 98)."
 */

#include <stdint.h>

typedef uint8_t u8;
typedef uint64_t u64;

u64 tnum_add_v(u64 av, u64 am, u64 bv, u64 bm)
{
	u64 sm, sv, sigma, chi, mu;

	sm = am + bm;
	sv = av + bv;
	sigma = sm + sv;
	chi = sigma ^ sv;
	mu = chi | am | bm;
	return sv & ~mu;
}

u64 tnum_add_m(u64 av, u64 am, u64 bv, u64 bm)
{
	u64 sm, sv, sigma, chi, mu;

	sm = am + bm;
	sv = av + bv;
	sigma = sm + sv;
	chi = sigma ^ sv;
	mu = chi | am | bm;
	return mu;
}

/* TODO REM */
u64 tnum_add_masks(u64 av, u64 am, u64 bv, u64 bm)
{
	return am + bm;
}
