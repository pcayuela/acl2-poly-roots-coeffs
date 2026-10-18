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

;; ---------------------------------------------------------------------------
;; Reversal is a permutation, so the reversal theorem of poly-roots-coeffs
;; (POLY-FROM-ROOTS-REVERSE-INVARIANT) is a special case of the theorem above.
;; PERMP is shown equivalent to equality of occurrence counts.

(defun cnt (a x)
  (cond ((atom x) 0)
        ((equal a (car x)) (+ 1 (cnt a (cdr x))))
        (t (cnt a (cdr x)))))

(defthm cnt-remove1-equal
  (equal (cnt b (remove1-equal a y))
         (if (member-equal a y)
             (if (equal a b) (+ -1 (cnt b y)) (cnt b y))
           (cnt b y))))

(defthm cnt-append
  (equal (cnt a (append x y)) (+ (cnt a x) (cnt a y))))

(defthm cnt-rev
  (equal (cnt a (rev x)) (cnt a x)))

(defthm cnt-member
  (implies (< 0 (cnt a y)) (member-equal a y)))

(defthm true-listp-remove1-equal-tl
  (implies (true-listp y) (true-listp (remove1-equal a y))))

(defun-sk cnt-equiv (x y)
  (forall a (equal (cnt a x) (cnt a y))))

(defthm cnt-equiv-cdr-remove1
  (implies (and (consp x) (cnt-equiv x y))
           (cnt-equiv (cdr x) (remove1-equal (car x) y)))
  :hints (("Goal" :expand ((cnt-equiv (cdr x) (remove1-equal (car x) y)))
                  :use ((:instance cnt-equiv-necc
                                   (a (cnt-equiv-witness (cdr x) (remove1-equal (car x) y))))
                        (:instance cnt-equiv-necc (a (car x)))))))

(defthm cnt-equiv-car-member
  (implies (and (consp x) (cnt-equiv x y))
           (member-equal (car x) y))
  :hints (("Goal" :use ((:instance cnt-equiv-necc (a (car x)))
                        (:instance cnt-member (a (car x)))))))

(defthm cnt-equiv-atom
  (implies (and (not (consp x)) (true-listp y) (cnt-equiv x y))
           (not (consp y)))
  :hints (("Goal" :use ((:instance cnt-equiv-necc (a (car y)))))))

(defthm cnt-equiv-implies-permp
  (implies (and (true-listp x) (true-listp y) (cnt-equiv x y))
           (permp x y))
  :hints (("Goal" :induct (permp x y)
                  :in-theory (disable cnt-equiv cnt-equiv-necc))))

(defthm cnt-equiv-rev
  (cnt-equiv x (rev x))
  :hints (("Goal" :expand ((cnt-equiv x (rev x))))))

(defthm permp-rev
  (implies (true-listp x) (permp x (rev x)))
  :hints (("Goal" :use (cnt-equiv-rev
                        (:instance cnt-equiv-implies-permp (y (rev x)))))))

;; The reversal theorem again, now as a corollary.
(defthm poly-from-roots-reverse-invariant-from-permp
  (implies (true-listp roots)
           (equal (poly-from-roots (rev roots)) (poly-from-roots roots)))
  :hints (("Goal" :use (permp-rev poly-from-roots-permutation-invariant)
                  :in-theory (disable permp-rev poly-from-roots-permutation-invariant))))

;; Ground checks
(assert-event (permp '(3 -5 -11 -1) '(-11 3 -1 -5)))
(assert-event (not (permp '(1 2 3) '(1 2 4))))
(assert-event (equal (poly-from-roots '(-11 3 -1 -5)) '(-165 -158 20 14 1)))
