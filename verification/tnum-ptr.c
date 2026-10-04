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

struct tnum {
	u64 value;
	u64 mask;
};

void tnum_add(struct tnum *a, struct tnum *b, struct tnum *r)
{
	u64 av = a->value;
	u64 am = a->mask;
	u64 bv = b->value;
	u64 bm = b->mask;

	u64 sm, sv, sigma, chi, mu;

	sm = am + bm;
	sv = av + bv;
	sigma = sm + sv;
	chi = sigma ^ sv;
	mu = chi | am | bm;

	r->value = sv & ~mu;
	r->mask = mu;
}
