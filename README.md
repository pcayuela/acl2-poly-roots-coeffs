# Polynomial coefficients from roots in ACL2

ACL2 formalization of the table-based construction of the coefficients of a
monic polynomial from its roots, from the Spanish-language CVM 2026 papers by
P. O. Cayuela (derivation and first ACL2 verification).

## Branches

* **`main`** keeps the book `poly-roots-coeffs.lisp` exactly as published and
  cited in the CVM 2026 verification paper. Its only change since then is the
  sign fix in `recursive_coefficientsv2.py` (`(-1)**(n - p)` instead of
  `(-1)**p`, wrong for odd degree).
* **`rumpsession`** (this branch) contains the work done for the ACL2 2026
  Workshop rump session: the extended development below.

## What this branch adds

| File | Content |
|------|---------|
| `poly-roots-coeffs.lisp` | the original book with guards verified, the new theorem `cardano-vieta` (each coefficient is `(-1)^(n-k) * (elem-sym (n-k) roots)`), corrected comments about the order of the factors, and simplified proofs (one global `in-theory` event; no theorem statement of the original changed) |
| `poly-roots-nested-sums.lisp` | the two nested sum-product formulas of the paper (eqs. (6) and (7)) as `desc-sum` and `asc-sum`, proved for every n and every p to equal the table coefficients up to `(-1)^(n-p)`, hence equal to each other |
| `poly-roots-permutations.lisp` | order independence for arbitrary permutations of the roots, with the community `perm` (`kestrel/lists-light/perm`); the reversal theorem and the symmetry of `elem-sym` follow as corollaries |
| `recursive_coefficientsv2.py` | the Python cross-check (sign fixed, as on `main`) |

## Certifying

The books certify with ACL2 8.7 and with ACL2(r) 8.7(r) (the theorems are about
`acl2-numberp`, so they cover irrational and complex roots in ACL2(r)).
From this directory, with the community books built:

    cert.pl poly-roots-nested-sums poly-roots-permutations

(`poly-roots-permutations.lisp` needs `kestrel/lists-light/perm` and `perm2`
from the community books.)

## Development

The books were developed with the AI coding agent Claude Code driving a live
ACL2 session through an MCP server. Only ACL2's certification counts as
validation of the theorems; the correspondence between the theorem statements
and the claims of the paper was checked by the author and by the reviewers of
the workshop.
