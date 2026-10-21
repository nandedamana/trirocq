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

/* Returns a tnum with the uncertainty from both a and b, and in addition, new
 * uncertainty at any position that a and b disagree. This represents a
 * superset of the union of the concrete sets of both a and b. Despite the
 * overapproximation, it is optimal.
 */
void tnum_union(struct tnum *a, struct tnum *b, struct tnum *r)
{
	u64 v = a->value & b->value;
	u64 mu = (a->value ^ b->value) | a->mask | b->mask;

	r->value = v & ~mu;
	r->mask = mu;
}

void tnum_lshift(struct tnum *a, u8 shift, struct tnum *r)
{
	r->value = a->value << shift;
	r->mask = a->mask << shift;
}

void tnum_rshift(struct tnum *a, u8 shift, struct tnum *r)
{
	r->value = a->value >> shift;
	r->mask = a->mask >> shift;
}

// Recursive function that implements the loop in the new algorithm
void tnum_mul_loop(u64 m, struct tnum *a, struct tnum *b, struct tnum *r)
{
	if (m != 0) {
		// kernel code uses `||`, but that will result in a nested if.
		// The equivalence has been shown in Rocq.
		if (a->value | a->mask) {
			struct tnum ap, bp; /* a', b' */
			ap.value = a->value;
			ap.mask = a->mask;
			bp.value = b->value;
			bp.mask = b->mask;

			/* LSB of tnum a is a certain 1 */
			if (ap.value & 1) {
				struct tnum sum;
				tnum_add(r, &bp, &sum);

				r->value = sum.value;
				r->mask = sum.mask;

				// BEGIN duplicate (code duplicated in both branches;
				// if there is code following an `if`, VST will make
				// us give the postcondition explicitly).
				struct tnum apsh, bpsh;
				tnum_rshift(&ap, 1, &apsh);
				tnum_lshift(&bp, 1, &bpsh);
				tnum_mul_loop(m - 1, &apsh, &bpsh, r);
				// END duplicate

			}
			/* LSB of tnum a is uncertain */
			else if (ap.mask & 1) {
				/* acc = tnum_union(acc_0, acc_1), where acc_0 and
				 * acc_1 are partial accumulators for cases
				 * LSB(a) = certain 0 and LSB(a) = certain 1.
				 * acc_0 = acc + 0 * b = acc.
				 * acc_1 = acc + 1 * b = tnum_add(acc, b).
				 */

				struct tnum sum, joined;
				tnum_add(r, &bp, &sum);
				tnum_union(r, &sum, &joined);

				r->value = joined.value;
				r->mask = joined.mask;

				// BEGIN duplicate (code duplicated in both branches;
				// if there is code following an `if`, VST will make
				// us give the postcondition explicitly).
				struct tnum apsh, bpsh;
				tnum_rshift(&ap, 1, &apsh);
				tnum_lshift(&bp, 1, &bpsh);
				tnum_mul_loop(m - 1, &apsh, &bpsh, r);
				// END duplicate
			}
			else {
				// BEGIN duplicate (code duplicated in both branches;
				// if there is code following an `if`, VST will make
				// us give the postcondition explicitly).
				struct tnum apsh, bpsh;
				tnum_rshift(&ap, 1, &apsh);
				tnum_lshift(&bp, 1, &bpsh);
				tnum_mul_loop(m - 1, &apsh, &bpsh, r);
				// END duplicate
			}
		}
	}
}

void tnum_mul(struct tnum *a, struct tnum *b, struct tnum *r)
{
	r->value = 0u;
	r->mask = 0u;
	tnum_mul_loop(64, a, b, r);
}
