;; ===========================================================================
;; poly-roots-permutations.lisp
;;
;; Order independence of the table construction for ARBITRARY permutations
;; of the roots (poly-roots-coeffs.lisp proves it only for reversal), and,
;; as a corollary through Cardano-Vieta, symmetry of the elementary
;; symmetric functions ELEM-SYM.
;;
;; PERMP is the usual multiset equality (each element of X is removed once
;; from Y).  The proof needs only MULT-BY-ROOT-COMMUTES: a root can be
;; pulled out of the middle of a list and applied last.
;; ===========================================================================

(in-package "ACL2")
(include-book "poly-roots-coeffs")

(set-verify-guards-eagerness 0)

(defun permp (x y)
  (cond ((atom x) (atom y))
        ((member-equal (car x) y) (permp (cdr x) (remove1-equal (car x) y)))
        (t nil)))

(defthm poly-from-roots-remove1
  (implies (member-equal a y)
           (equal (poly-from-roots y)
                  (mult-by-root (poly-from-roots (remove1-equal a y)) a)))
  :hints (("Goal" :induct (poly-from-roots y)
                  :in-theory (disable mult-by-root mult-by-root-as-poly-add))))

(defthm poly-from-roots-permutation-invariant
  (implies (permp x y)
           (equal (poly-from-roots x) (poly-from-roots y)))
  :hints (("Goal" :induct (permp x y)
                  :in-theory (disable mult-by-root mult-by-root-as-poly-add))))

(defthm len-remove1-equal-member
  (implies (member-equal a y)
           (equal (len (remove1-equal a y)) (+ -1 (len y)))))

(defthm permp-len
  (implies (permp x y) (equal (len x) (len y)))
  :hints (("Goal" :induct (permp x y))))

;; The elementary symmetric functions are symmetric.
(defthm elem-sym-permutation-invariant
  (implies (and (permp x y) (number-listp x) (number-listp y)
                (natp k) (<= k (len x)))
           (equal (elem-sym k x) (elem-sym k y)))
  :hints (("Goal" :use ((:instance cardano-vieta (roots x) (k (- (len x) k)))
                        (:instance cardano-vieta (roots y) (k (- (len x) k)))
                        poly-from-roots-permutation-invariant
                        permp-len)
                  :in-theory (disable cardano-vieta poly-from-roots-permutation-invariant
                                      permp-len))))

;; Ground checks
(assert-event (permp '(3 -5 -11 -1) '(-11 3 -1 -5)))
(assert-event (not (permp '(1 2 3) '(1 2 4))))
(assert-event (equal (poly-from-roots '(-11 3 -1 -5)) '(-165 -158 20 14 1)))
