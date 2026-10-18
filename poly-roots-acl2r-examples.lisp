;; ===========================================================================
;; poly-roots-acl2r-examples.lisp   (ACL2(r) only)
;;
;; The theorems of poly-roots-coeffs, poly-roots-nested-sums and
;; poly-roots-permutations quantify over all ACL2 numbers (ACL2-NUMBERP).
;; In plain ACL2 those are the rationals and complex rationals, so the
;; theorems never reach a polynomial such as x^2 - 2: there is no ACL2
;; number whose square is 2 (THERE-IS-NO-SQRT-2 in nonstd/nsa/sqrt-2).
;; The same books certify unchanged in ACL2(r), where ACL2-NUMBERP includes
;; the irrational reals and the complex numbers built from them.  This book
;; shows that the hypotheses are then met by irrational and complex roots,
;; as the poles of a control system are, and computes two such tables.
;; ===========================================================================

; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "poly-roots-coeffs")
(include-book "poly-roots-nested-sums")
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "nonstd/nsa/sqrt-2" :dir :system)

;; ---------------------------------------------------------------------------
;; sqrt(2) exists in ACL2(r), and it is irrational.

(defthm sqrt-2-squared
  (equal (* (acl2-sqrt 2) (acl2-sqrt 2)) 2)
  :hints (("Goal" :use (:instance sqrt-=-y (x 2) (y (acl2-sqrt 2))))))

(defthm sqrt-2-is-irrational
  (and (realp (acl2-sqrt 2))
       (not (rationalp (acl2-sqrt 2))))
  :hints (("Goal" :use (:instance irrational-sqrt-2 (x (acl2-sqrt 2))))))

;; ---------------------------------------------------------------------------
;; Roots +sqrt(2), -sqrt(2): the table gives x^2 - 2.

(defthm poly-from-roots-plus-minus-sqrt-2
  (equal (poly-from-roots (list (acl2-sqrt 2) (- (acl2-sqrt 2))))
         '(-2 0 1))
  :hints (("Goal" :in-theory (enable poly-add poly-scale poly-shift
                                     mult-by-root))))

;; The hypothesis of CARDANO-VIETA and of the nested-sum theorems holds for
;; this irrational root list, so they apply to it.
(defthm sqrt-2-roots-satisfy-the-hypotheses
  (and (number-listp (list (acl2-sqrt 2) (- (acl2-sqrt 2))))
       (not (rationalp (acl2-sqrt 2)))))

(defthm sqrt-2-constant-term-by-cardano-vieta
  (equal (* (expt -1 2) (elem-sym 2 (list (acl2-sqrt 2) (- (acl2-sqrt 2)))))
         -2))

;; ---------------------------------------------------------------------------
;; A pair of complex conjugate poles sigma +/- j omega, with sigma and
;; omega any reals: the table gives x^2 - 2 sigma x + (sigma^2 + omega^2).

(defthm poly-from-roots-conjugate-pair
  (implies (and (realp s) (realp w))
           (equal (poly-from-roots (list (complex s w) (complex s (- w))))
                  (list (+ (* s s) (* w w)) (* -2 s) 1)))
  :hints (("Goal" :in-theory (enable poly-add poly-scale poly-shift
                                     mult-by-root)
                  :use ((:instance complex-definition (x s) (y w))
                        (:instance complex-definition (x s) (y (- w)))))))

;; Poles -1 +/- j sqrt(2), with an irrational imaginary part:
;; x^2 + 2x + 3.
(defthm poly-from-roots-poles-minus-1-plus-minus-j-sqrt-2
  (equal (poly-from-roots (list (complex -1 (acl2-sqrt 2))
                                (complex -1 (- (acl2-sqrt 2)))))
         '(3 2 1))
  :hints (("Goal" :use (:instance poly-from-roots-conjugate-pair
                                  (s -1) (w (acl2-sqrt 2))))))
