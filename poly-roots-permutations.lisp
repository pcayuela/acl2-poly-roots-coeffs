;; ===========================================================================
;; poly-roots-permutations.lisp
;;
;; Order independence of the table construction for ARBITRARY permutations
;; of the roots (poly-roots-coeffs.lisp proves it only for reversal), the
;; reversal theorem as a special case, and, as a corollary through
;; Cardano-Vieta, symmetry of the elementary symmetric functions ELEM-SYM.
;;
;; PERM is the community-books permutation relation (Eric Smith, Kestrel,
;; kestrel/lists-light/perm): each element of X is removed once from Y.
;; The proof needs only MULT-BY-ROOT-COMMUTES: a root can be pulled out of
;; the middle of a list and applied last.
;; ===========================================================================

(in-package "ACL2")
(include-book "poly-roots-coeffs")
(include-book "kestrel/lists-light/perm" :dir :system)
(include-book "kestrel/lists-light/perm2" :dir :system)

(set-verify-guards-eagerness 0)

(defthm poly-from-roots-remove1
  (implies (member-equal a y)
           (equal (poly-from-roots y)
                  (mult-by-root (poly-from-roots (remove1-equal a y)) a)))
  :hints (("Goal" :induct (poly-from-roots y)
                  :in-theory (disable mult-by-root mult-by-root-as-poly-add))))

(defthm poly-from-roots-permutation-invariant
  (implies (perm x y)
           (equal (poly-from-roots x) (poly-from-roots y)))
  :hints (("Goal" :induct (perm x y)
                  :in-theory (e/d (perm) (mult-by-root mult-by-root-as-poly-add)))))

;; ACL2 can now reorder the roots by itself inside any expression.
(defcong perm equal (poly-from-roots x) 1
  :hints (("Goal" :use (:instance poly-from-roots-permutation-invariant (y x-equiv)))))

;; Reversal is a permutation, so the reversal theorem is a corollary.
(defthm perm-rev
  (perm (rev x) x)
  :hints (("Goal" :induct (rev x))))

(defthm poly-from-roots-reverse-invariant-from-perm
  (equal (poly-from-roots (rev roots)) (poly-from-roots roots))
  :hints (("Goal" :use (:instance poly-from-roots-permutation-invariant
                                  (x (rev roots)) (y roots))
                  :in-theory (disable poly-from-roots-permutation-invariant))))

;; The elementary symmetric functions are symmetric.
(defthm len-when-perm
  (implies (perm x y) (equal (len x) (len y)))
  :hints (("Goal" :induct (perm x y) :in-theory (enable perm))))

(defthm elem-sym-permutation-invariant
  (implies (and (perm x y) (number-listp x) (number-listp y)
                (natp k) (<= k (len x)))
           (equal (elem-sym k x) (elem-sym k y)))
  :hints (("Goal" :use ((:instance cardano-vieta (roots x) (k (- (len x) k)))
                        (:instance cardano-vieta (roots y) (k (- (len x) k)))
                        poly-from-roots-permutation-invariant
                        len-when-perm)
                  :in-theory (disable cardano-vieta poly-from-roots-permutation-invariant
                                      len-when-perm))))

;; Ground checks
(assert-event (perm '(3 -5 -11 -1) '(-11 3 -1 -5)))
(assert-event (not (perm '(1 2 3) '(1 2 4))))
(assert-event (equal (poly-from-roots '(-11 3 -1 -5)) '(-165 -158 20 14 1)))
