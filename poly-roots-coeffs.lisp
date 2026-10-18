;; ===========================================================================
;; poly-roots-coeffs.lisp
;;
;; ACL2 formalization and verification of the results in:
;;   "Calculo de los coeficientes de un polinomio a partir de sus raices:
;;    construccion por tabla de multiplicacion y verificacion de dos
;;    lecturas equivalentes" (P. O. Cayuela).
;;
;; This book formalizes, over an unbounded number n of symbolic roots
;; a1,...,an (ACL2 does not need n to be fixed: all theorems below are
;; proved by induction on the list of roots, i.e. for every n at once):
;;
;;   (1) The "table of successive multiplication" construction of
;;       P(x) = prod_{i=1}^n (x - a_i)  (paper's Tables I and III,
;;       and the recurrence bp^(n) = bp-1^(n-1) - an*bp^(n-1), eq. (5)),
;;       and its soundness: the coefficients it builds really do define
;;       the polynomial whose value is that product, for every x.
;;
;;   (2) The classical Cardano-Vieta relation bi = (-1)^(n-i) * e_(n-i)(a)
;;       between those coefficients and the elementary symmetric
;;       functions of the roots (paper's eq. (3)).
;;
;;   (3) The central claim of the paper's Section VI: the descending
;;       reading (grouping the summands by the highest root index first;
;;       the roots are multiplied in as a1, a2, ..., an, so an is the
;;       outermost factor) and the ascending reading (grouping by the
;;       lowest root index first; a1 is the outermost factor) of the same
;;       table are equivalent, because they amount to building the same
;;       product of linear factors in opposite order. This is formalized
;;       as order-independence of the table construction:
;;           (poly-from-roots roots) = (poly-from-roots (rev roots))
;;
;; -----------------------------------------------------------------------
;; STATUS OF THIS FILE
;;
;; This file has been run through a live, interactive ACL2 session (via
;; the ACL2-MCP server) and every DEFTHM below is a certified theorem --
;; ACL2 printed "Q.E.D." for each one. A number of the original
;; conjectures needed genuine strengthening (not just new hints) to be
;; true as stated:
;;
;;   - Several lemmas about POLY-ADD (commutativity, associativity, and
;;     anything built on them) only hold for TRUE-LISTP arguments: with
;;     no hypothesis, POLY-ADD's "return the other argument once one
;;     list runs out" base case is not actually commutative/associative
;;     for arbitrary (possibly improper or dotted) ACL2 objects.
;;   - Facts that pick out a specific list element (NTH-POLY-ADD and
;;     everything downstream of it, in particular
;;     CAR-LAST-POLY-FROM-ROOTS-IS-ONE) additionally need the
;;     coefficients to be NUMBER-LISTP: ACL2's "+" silently coerces a
;;     non-number (in particular NIL, which is what NTH returns past
;;     the end of a list) to 0, so an equation that is numerically true
;;     can still fail as a literal EQUAL unless the elements are known
;;     to be ACL2 numbers.
;;   - A handful of auxiliary lemmas (list-length and nth-in-range
;;     facts, type-preservation facts for the coefficient-list
;;     constructors, etc.) were missing entirely and had to be added;
;;     these are ordinary induction exercises with no surprising content.
;;
;; None of this changes the mathematical content of the paper: roots and
;; coefficients are always numbers and lists in the intended reading, so
;; every added hypothesis is satisfied in exactly the situations the
;; paper cares about (see PART IV for the concrete numeric instance).
;;
;; To certify:
;;     (certify-book "poly-roots-coeffs")
;; run from an ACL2 session in this file's directory.
;; ===========================================================================

(in-package "ACL2")

;; Every DEFUN below declares a :guard (NUMBER-LISTP for coefficient and
;; root lists, since the functions add and multiply the elements).
;; Guard verification is deferred to PART III-B at the end of the
;; development, once the type-preservation lemmas it needs have been
;; proved; the logical definitions and all theorems are unaffected.
(set-verify-guards-eagerness 0)

;; A recognizer for lists whose every element is an ACL2 number. Needed
;; because NTH past the end of a list returns NIL, and ACL2's "+"
;; silently coerces a non-number to 0 -- so an equation like
;; (nth i (poly-add p q)) = (+ (nth i p) (nth i q)) can only hold as a
;; literal EQUAL when the elements involved are genuinely numbers. It is
;; also the guard of the list-processing functions below, so it is a
;; PROPER list recognizer (the empty case requires NIL, not just any
;; atom): that is what makes ENDP's guard provable from it.
(defun number-listp (l)
  (declare (xargs :guard t))
  (if (consp l) (and (acl2-numberp (car l)) (number-listp (cdr l))) (null l)))

;; ===========================================================================
;; PART 0 -- Polynomials as coefficient lists
;;
;; A polynomial is represented as a list of coefficients, constant term
;; first:  (c0 c1 c2 ... cd)  represents  c0 + c1*x + c2*x^2 + ... + cd*x^d.
;; ===========================================================================

;; Evaluate a polynomial (coefficient list) at a point x. Horner's rule.
(defun poly-eval (coeffs x)
  (declare (xargs :guard (and (acl2-numberp x) (number-listp coeffs))))
  (if (endp coeffs)
      0
    (+ (car coeffs) (* x (poly-eval (cdr coeffs) x)))))

;; Add two coefficient lists (pointwise, padding the shorter one with 0s).
(defun poly-add (p q)
  (declare (xargs :guard (and (number-listp p) (number-listp q))))
  (cond ((endp p) q)
        ((endp q) p)
        (t (cons (+ (car p) (car q)) (poly-add (cdr p) (cdr q))))))

;; Scale every coefficient by a constant c.
(defun poly-scale (p c)
  (declare (xargs :guard (and (number-listp p) (acl2-numberp c))))
  (if (endp p)
      nil
    (cons (* c (car p)) (poly-scale (cdr p) c))))

;; Negate every coefficient.
(defun poly-neg (p)
  (declare (xargs :guard (number-listp p)))
  (poly-scale p -1))

;; Multiply by x, i.e. raise every term's degree by one (prepend a 0).
(defun poly-shift (p)
  (declare (xargs :guard (number-listp p)))
  (cons 0 p))

;; Multiply the polynomial `coeffs' by the linear factor (x - a):
;;    (x - a) * P(x)  =  x*P(x)  -  a*P(x)  =  shift(P) + scale(P, -a)
(defun mult-by-root (coeffs a)
  (declare (xargs :guard (and (number-listp coeffs) (acl2-numberp a))))
  (poly-add (poly-shift coeffs) (poly-scale coeffs (- a))))

;; ---------------------------------------------------------------------------
;; Basic algebraic facts about poly-add / poly-scale / poly-shift.
;; These are the "linear algebra of coefficient lists" lemmas used to
;; prove everything else; each is a routine induction.
;;
;; POLY-ADD-COMMUTATIVE and POLY-ADD-ASSOCIATIVE need TRUE-LISTP
;; hypotheses: without them, POLY-ADD's base case (return whichever
;; argument ran out first, unmodified) is not actually symmetric for
;; arbitrary non-list ACL2 objects, e.g. (poly-add 'a nil) = nil but
;; (poly-add nil 'a) = 'a.
;; ---------------------------------------------------------------------------

(defthm poly-add-commutative
  (implies (and (true-listp p) (true-listp q))
           (equal (poly-add p q) (poly-add q p)))
  :hints (("Goal" :induct (poly-add p q))))

;; Helper induction scheme for POLY-ADD-ASSOCIATIVE: the natural
;; 2-argument induction ACL2 derives from POLY-ADD does not track all
;; three lists shrinking together, so we supply an explicit induction
;; that cdrs P, Q and R in lockstep.
(defun triple-add-induct (p q r)
  (declare (xargs :guard (and (number-listp p) (number-listp q) (number-listp r))))
  (cond ((endp p) (list p q r))
        ((endp q) (list p q r))
        ((endp r) (list p q r))
        (t (triple-add-induct (cdr p) (cdr q) (cdr r)))))

(defthm poly-add-associative
  (implies (and (true-listp p) (true-listp q) (true-listp r))
           (equal (poly-add (poly-add p q) r) (poly-add p (poly-add q r))))
  :hints (("Goal" :induct (triple-add-induct p q r))))

(defthm poly-scale-over-poly-add
  (equal (poly-scale (poly-add p q) c)
         (poly-add (poly-scale p c) (poly-scale q c)))
  :hints (("Goal" :induct (poly-add p q))))

(defthm poly-shift-over-poly-add
  (equal (poly-shift (poly-add p q))
         (poly-add (poly-shift p) (poly-shift q))))

(defthm poly-shift-poly-scale
  (equal (poly-shift (poly-scale p c))
         (poly-scale (poly-shift p) c)))

;; POLY-SCALE-POLY-SCALE needs to reorder a three-variable product
;; ((* d c x) = (* x c d)); ACL2's built-in commutativity/associativity
;; rules for "*" cannot always find this rearrangement by themselves
;; (it depends on ACL2's internal term order), so we bring in the
;; standard nonlinear-arithmetic normalization book.
(include-book "arithmetic/top-with-meta" :dir :system)

(defthm poly-scale-poly-scale
  (equal (poly-scale (poly-scale p c) d)
         (poly-scale p (* c d)))
  :hints (("Goal" :induct (poly-scale p c))))

;; How poly-eval interacts with the three building blocks: this is what
;; turns "coefficient-list algebra" into "polynomial-value algebra".

(defthm poly-eval-poly-add
  (equal (poly-eval (poly-add p q) x)
         (+ (poly-eval p x) (poly-eval q x)))
  :hints (("Goal" :induct (poly-add p q))))

(defthm poly-eval-poly-scale
  (equal (poly-eval (poly-scale p c) x)
         (* c (poly-eval p x))))

(defthm poly-eval-poly-shift
  (equal (poly-eval (poly-shift p) x)
         (* x (poly-eval p x))))

;; Soundness of mult-by-root: evaluating (x - a)*P really does give
;; (x - a) times the value of P.
(defthm poly-eval-mult-by-root
  (equal (poly-eval (mult-by-root coeffs a) x)
         (* (- x a) (poly-eval coeffs x))))

;; mult-by-root's own definition, restated as a plain (unconditional)
;; rewrite rule expanded purely in terms of poly-add/poly-shift/poly-scale.
;; Used throughout the rest of the book to reason about mult-by-root
;; algebraically without ever unfolding poly-add's recursive definition
;; (which tends to blow up the proof search with case splits).
(defthm mult-by-root-as-poly-add
  (equal (mult-by-root p a) (poly-add (poly-shift p) (poly-scale p (- a))))
  :hints (("Goal" :in-theory (enable mult-by-root))))

(defthm true-listp-poly-add
  (implies (and (true-listp p) (true-listp q))
           (true-listp (poly-add p q))))

;; Helper reassociation fact used by MULT-BY-ROOT-COMMUTES: swapping the
;; two middle terms of a 4-way sum. Proved once here from
;; POLY-ADD-ASSOCIATIVE/POLY-ADD-COMMUTATIVE instead of being
;; rediscovered by induction at every use site.
(defthm poly-add-swap-middle-core
  (implies (and (true-listp x) (true-listp y) (true-listp z))
           (equal (poly-add x (poly-add y z)) (poly-add y (poly-add x z))))
  :hints (("Goal" :use ((:instance poly-add-associative (p x) (q y) (r z))
                        (:instance poly-add-associative (p y) (q x) (r z))
                        (:instance poly-add-commutative (p x) (q y)))
                  :in-theory (disable poly-add-associative poly-add-commutative poly-add))))

(defthm poly-add-swap-middle
  (implies (and (true-listp w) (true-listp x) (true-listp y) (true-listp z))
           (equal (poly-add w (poly-add x (poly-add y z)))
                  (poly-add w (poly-add y (poly-add x z)))))
  :hints (("Goal" :use ((:instance poly-add-swap-middle-core))
                  :in-theory (disable poly-add))))

;; mult-by-root commutes with multiplying by two different roots, in
;; either order -- because polynomial multiplication is commutative.
;; This is the key step for proving the table construction does not
;; depend on the order in which the roots are processed. Needs
;; TRUE-LISTP P for the same reason POLY-ADD-COMMUTATIVE/ASSOCIATIVE do.
(defthm mult-by-root-commutes
  (implies (true-listp p)
           (equal (mult-by-root (mult-by-root p a) b)
                  (mult-by-root (mult-by-root p b) a)))
  :hints (("Goal" :in-theory (e/d (mult-by-root-as-poly-add)
                                   (poly-add mult-by-root))
                  :use ((:instance poly-add-associative
                            (p (poly-shift (poly-shift p)))
                            (q (poly-scale (poly-shift p) (- a)))
                            (r (poly-add (poly-scale (poly-shift p) (- b)) (poly-scale p (* a b)))))
                        (:instance poly-add-associative
                            (p (poly-shift (poly-shift p)))
                            (q (poly-scale (poly-shift p) (- b)))
                            (r (poly-add (poly-scale (poly-shift p) (- a)) (poly-scale p (* a b)))))
                        (:instance poly-add-swap-middle
                            (w (poly-shift (poly-shift p)))
                            (x (poly-scale (poly-shift p) (- a)))
                            (y (poly-scale (poly-shift p) (- b)))
                            (z (poly-scale p (* a b))))))))

;; mult-by-root is linear in its coefficient-list argument.
(defthm mult-by-root-poly-scale
  (equal (mult-by-root (poly-scale p c) a)
         (poly-scale (mult-by-root p a) c))
  :hints (("Goal" :in-theory (enable mult-by-root))))


;; ===========================================================================
;; PART I -- The table of successive multiplication (paper's Tables I, III
;;           and the recurrence (5))
;; ===========================================================================

;; Build P(x) = prod_{a in roots} (x - a) by multiplying in the n
;; factors one at a time, one row of Table I / Table III per factor.
;; Order of the factors: the recursion peels the FIRST root off the front,
;; so poly-from-roots(a1 a2 ... an) = mult-by-root(poly-from-roots(a2 ... an), a1):
;; the first-applied factor is the LAST root an and a1 is multiplied in last
;; (a1 is the outermost factor: the paper's ascending reading).  The
;; paper's recurrence  bp^(n) = bp-1^(n-1) - an * bp^(n-1),  bn^(n) = 1
;; multiplies in a1, a2, ..., an in that order, with an outermost (the
;; descending reading): that order is (poly-from-roots (rev (a1 ... an))).
;; Both orders give the same coefficients (Theorem 3 below).
(defun poly-from-roots (roots)
  (declare (xargs :guard (number-listp roots)))
  (if (endp roots)
      (list 1)
    (mult-by-root (poly-from-roots (cdr roots)) (car roots))))

;; The "obviously correct" reference specification: the product of the
;; linear factors, evaluated directly.
(defun prod-factors (roots x)
  (declare (xargs :guard (and (number-listp roots) (acl2-numberp x))))
  (if (endp roots)
      1
    (* (- x (car roots)) (prod-factors (cdr roots) x))))

;; Type-preservation lemmas for poly-from-roots, needed by the
;; soundness/degree/leading-coefficient theorems below.
(defthm true-listp-poly-shift
  (implies (true-listp p) (true-listp (poly-shift p))))

(defthm true-listp-mult-by-root
  (implies (true-listp p) (true-listp (mult-by-root p a)))
  :hints (("Goal" :in-theory (enable mult-by-root))))

(defthm true-listp-poly-from-roots
  (true-listp (poly-from-roots roots)))

(defthm consp-mult-by-root
  (consp (mult-by-root p a))
  :hints (("Goal" :in-theory (enable mult-by-root))))

(defthm consp-poly-scale
  (equal (consp (poly-scale p c)) (consp p)))

(defthm acl2-numberp-car-poly-scale
  (implies (consp p)
           (acl2-numberp (car (poly-scale p c)))))

;; -----------------------------------------------------------------
;; THEOREM 1 (soundness of the table construction; paper's eq. (1)-(2)
;; and Tables I/III): the polynomial built by the table/recurrence
;; evaluates, at every x, to the product of the linear factors.
;; -----------------------------------------------------------------
(defthm poly-from-roots-correct
  (equal (poly-eval (poly-from-roots roots) x)
         (prod-factors roots x)))

;; The degree is always exactly n = (len roots), and the leading
;; coefficient is 1 (P is monic) -- a companion sanity check.

(defthm len-poly-add
  (equal (len (poly-add p q))
         (if (< (len p) (len q)) (len q) (len p)))
  :hints (("Goal" :induct (poly-add p q))))

(defthm len-poly-scale
  (equal (len (poly-scale p c)) (len p)))

(defthm len-cdr-poly-scale
  (implies (consp p)
           (equal (len (cdr (poly-scale p c))) (1- (len p)))))

(defthm len-poly-from-roots
  (equal (len (poly-from-roots roots))
         (+ 1 (len roots))))

(defthm number-listp-poly-scale
  (number-listp (poly-scale p c)))

(defthm number-listp-poly-shift
  (implies (number-listp p) (number-listp (poly-shift p))))

(defthm number-listp-poly-add
  (implies (and (number-listp p) (number-listp q))
           (number-listp (poly-add p q))))

(defthm number-listp-mult-by-root
  (implies (number-listp p) (number-listp (mult-by-root p a)))
  :hints (("Goal" :in-theory (enable mult-by-root))))

(defthm number-listp-poly-from-roots
  (number-listp (poly-from-roots roots)))

(defthm acl2-numberp-nth-number-listp
  (implies (and (number-listp p) (natp i) (< i (len p)))
           (acl2-numberp (nth i p))))

;; nth-poly-add needs both NUMBER-LISTP (so out-of-range NIL entries
;; are correctly treated as the additive identity 0) and a non-negative
;; index (NTH treats a negative/non-integer index the same as index 0,
;; which breaks the formula when both lists are empty).
(defthm nth-poly-add
  (implies (and (number-listp p) (number-listp q)
                (natp i)
                (or (< i (len p)) (< i (len q))))
           (equal (nth i (poly-add p q))
                  (+ (nth i p) (nth i q)))))

(defthm consp-poly-from-roots
  (consp (poly-from-roots roots)))

(defthm nth-len-mult-by-root
  (implies (and (number-listp p) (consp p))
           (equal (nth (len p) (mult-by-root p a))
                  (nth (1- (len p)) p)))
  :hints (("Goal" :in-theory (e/d (mult-by-root-as-poly-add) (poly-add mult-by-root))
                  :use ((:instance nth-poly-add
                            (p (poly-shift p)) (q (poly-scale p (- a))) (i (len p)))))))

(defthm nth-out-of-range
  (implies (and (natp i) (<= (len p) i))
           (equal (nth i p) nil)))

(defthm number-listp-cdr
  (implies (number-listp l) (number-listp (cdr l))))

(defthm car-last-poly-from-roots-is-one
  (equal (nth (len roots) (poly-from-roots roots))
         1))


;; ===========================================================================
;; PART II -- Cardano-Vieta relation via the elementary symmetric
;;            functions of the roots (paper's eq. (3))
;; ===========================================================================

;; Negate every root.
(defun negate-list (lst)
  (declare (xargs :guard (number-listp lst)))
  (if (endp lst)
      nil
    (cons (- (car lst)) (negate-list (cdr lst)))))

;; Flip the sign of every other coefficient: (c0 c1 c2 c3 ...) becomes
;; (c0 -c1 c2 -c3 ...), i.e. coefficient i gets multiplied by (-1)^i.
(defun alternate-sign (coeffs)
  (declare (xargs :guard (number-listp coeffs)))
  (if (endp coeffs)
      nil
    (cons (car coeffs) (poly-neg (alternate-sign (cdr coeffs))))))

;; The elementary symmetric functions of the roots, e_k(a1,...,an):
;; the standard "include a1 in the product, or don't" recursion.
;; e_0 = 1 for any list; e_k of the empty list is 0 for k > 0.
(defun elem-sym (k lst)
  (declare (xargs :guard (and (natp k) (number-listp lst))))
  (cond ((zp k) 1)
        ((endp lst) 0)
        (t (+ (* (car lst) (elem-sym (1- k) (cdr lst)))
              (elem-sym k (cdr lst))))))

;; The coefficient list of prod (x + a_i): built with the same
;; recursion as poly-from-roots, but adding each root instead of
;; subtracting it. By construction this equals poly-from-roots of the
;; negated roots (proved just below), and its coefficients are exactly
;; the elem-sym values, matching the standard generating-function fact
;;    prod_{i=1}^n (x + a_i) = sum_{k=0}^n e_k(a) x^(n-k).
(defun elem-sym-list (roots)
  (declare (xargs :guard (number-listp roots)))
  (if (endp roots)
      (list 1)
    (mult-by-root (elem-sym-list (cdr roots)) (- (car roots)))))

(defthm elem-sym-list-is-poly-from-negated-roots
  (equal (elem-sym-list roots)
         (poly-from-roots (negate-list roots))))

;; -----------------------------------------------------------------
;; Key commutation lemma: alternating signs and multiplying by a root
;; interact with a sign flip -- alternate-sign(shift(P)) = -shift(neg...)
;; and alternate-sign(scale(P,c)) = scale(alternate-sign(P),c), combined
;; give:
;;     mult-by-root(alternate-sign(P), -r) = -alternate-sign(mult-by-root(P,r))
;; This was checked numerically (random polynomials and roots) before
;; being stated here.
;; -----------------------------------------------------------------
(defthm alternate-sign-poly-shift
  (equal (alternate-sign (poly-shift p))
         (poly-shift (poly-neg (alternate-sign p)))))

(defthm alternate-sign-poly-scale
  (equal (alternate-sign (poly-scale p c))
         (poly-scale (alternate-sign p) c)))

;; alternate-sign is additive over poly-add -- holds unconditionally
;; because both are elementwise, zero-padded operations on lists.
(defthm alternate-sign-poly-add
  (equal (alternate-sign (poly-add p q))
         (poly-add (alternate-sign p) (alternate-sign q))))

;; Scaling by 1 is the identity, for a NUMBER-LISTP TRUE-LISTP list
;; (needed so that (* 1 (car p)) simplifies back to the literal (car p)).
(defthm poly-scale-by-one
  (implies (and (number-listp p) (true-listp p))
           (equal (poly-scale p 1) p)))

(defthm number-listp-alternate-sign
  (implies (number-listp p) (number-listp (alternate-sign p))))

(defthm true-listp-alternate-sign
  (true-listp (alternate-sign p)))

;; shift and alternate-sign "almost" commute, up to an overall sign:
;; shift(alt(p)) = -alt(shift(p)). Derived from ALTERNATE-SIGN-POLY-SHIFT
;; by scaling both sides by -1 and using POLY-SCALE-POLY-SCALE /
;; POLY-SCALE-BY-ONE to cancel the double negation.
(defthm shift-alternate-sign
  (implies (and (number-listp p) (true-listp p))
           (equal (poly-shift (alternate-sign p))
                  (poly-scale (alternate-sign (poly-shift p)) -1)))
  :hints (("Goal" :in-theory (disable poly-add poly-scale poly-shift alternate-sign)
                  :use ((:instance alternate-sign-poly-shift)
                        (:instance poly-shift-poly-scale (p (alternate-sign p)) (c -1))
                        (:instance poly-scale-poly-scale
                                   (p (poly-shift (alternate-sign p))) (c -1) (d -1))
                        (:instance poly-scale-by-one (p (poly-shift (alternate-sign p))))))))

(defthm mult-by-root-alternate-sign
  (implies (and (number-listp p) (true-listp p))
           (equal (mult-by-root (alternate-sign p) (- r))
                  (poly-scale (alternate-sign (mult-by-root p r)) -1)))
  :hints (("Goal"
           :in-theory (e/d (mult-by-root-as-poly-add)
                            (poly-add poly-scale poly-shift alternate-sign mult-by-root
                                      alternate-sign-poly-shift shift-alternate-sign))
           :use ((:instance shift-alternate-sign)
                 (:instance alternate-sign-poly-add
                            (p (poly-shift p)) (q (poly-scale p (- r))))
                 (:instance alternate-sign-poly-scale (p p) (c (- r)))
                 (:instance poly-scale-over-poly-add
                            (p (alternate-sign (poly-shift p)))
                            (q (alternate-sign (poly-scale p (- r))))
                            (c -1))
                 (:instance poly-scale-poly-scale
                            (p (alternate-sign p)) (c (- r)) (d -1))))))

;; poly-from-roots and negate-list restated as flat (non-recursive)
;; rewrite rules on the CONSP/non-CONSP cases, used to control the
;; induction below without letting poly-add's own definition unfold.
(defthm poly-from-roots-cons
  (equal (poly-from-roots (cons a roots)) (mult-by-root (poly-from-roots roots) a))
  :hints (("Goal" :in-theory (enable poly-from-roots))))

(defthm negate-list-cons
  (equal (negate-list (cons a roots)) (cons (- a) (negate-list roots))))

(defthm poly-from-roots-of-endp
  (implies (not (consp roots)) (equal (poly-from-roots roots) (list 1)))
  :hints (("Goal" :in-theory (enable poly-from-roots))))

(defthm negate-list-of-endp
  (implies (not (consp roots)) (equal (negate-list roots) nil)))

;; -----------------------------------------------------------------
;; THEOREM 2 (Cardano-Vieta, list form; paper's eq. (3)): building the
;; polynomial from the negated roots gives, up to the overall sign
;; (-1)^n, the same list as flipping the sign of every other
;; coefficient of the original polynomial.
;;     poly-from-roots(-a1,...,-an)
;;         = (-1)^n * alternate-sign(poly-from-roots(a1,...,an))
;; This is the list form of the relation. Its coefficient form,
;;     bk = (-1)^(n-k) * ek(a1,...,an)   (paper's eq. (3)),
;; which mentions ELEM-SYM, is the theorem CARDANO-VIETA just below.
;; -----------------------------------------------------------------
(defthm cardano-vieta-list-form
  (equal (poly-from-roots (negate-list roots))
         (poly-scale (alternate-sign (poly-from-roots roots))
                      (expt -1 (len roots))))
  :hints (("Goal"
           :induct (poly-from-roots roots)
           :in-theory (disable poly-add poly-scale poly-shift mult-by-root
                                alternate-sign negate-list
                                mult-by-root-as-poly-add
                                (:definition poly-from-roots)))))


;; -----------------------------------------------------------------
;; THEOREM 2' (Cardano-Vieta, coefficient form; paper's eq. (3)): each
;; coefficient of poly-from-roots is, up to sign, an elementary
;; symmetric function of the roots:
;;     b_k = (-1)^(n-k) * e_(n-k)(a_1,...,a_n),   0 <= k <= n = (len roots).
;; Unlike CARDANO-VIETA-LIST-FORM above, which relates two products of
;; linear factors, this theorem mentions ELEM-SYM itself. It is proved
;; directly by induction on the roots, using the recursion
;;     e_j(a . r) = a * e_(j-1)(r) + e_j(r)
;; of ELEM-SYM and the coefficient-wise form of MULT-BY-ROOT.
;; -----------------------------------------------------------------

;; (-1)^(j+1) = -(-1)^j
(defthm expt--1-plus-1
  (implies (natp j)
           (equal (expt -1 (+ 1 j)) (- (expt -1 j)))))

;; e_k of a list with fewer than k elements is 0.
(defthm elem-sym-zero-above-length
  (implies (and (natp k) (< (len lst) k))
           (equal (elem-sym k lst) 0)))

;; Coefficient k of (x - a) * P(x): coefficient (k-1) of P, minus a
;; times coefficient k of P.
(defthm nth-mult-by-root
  (implies (and (number-listp p) (natp k) (<= k (len p)))
           (equal (nth k (mult-by-root p a))
                  (+ (if (zp k) 0 (nth (1- k) p))
                     (* (- a) (nth k p)))))
  :hints (("Goal" :in-theory (e/d (mult-by-root-as-poly-add)
                                  (poly-add mult-by-root))
                  :use ((:instance nth-poly-add
                          (p (poly-shift p)) (q (poly-scale p (- a))) (i k))))))

;; Induction scheme: the step needs the hypothesis at k and at k-1.
(defun cv-ind (roots k)
  (declare (xargs :measure (len roots)))
  (if (endp roots)
      k
    (cons (cv-ind (cdr roots) k)
          (cv-ind (cdr roots) (if (zp k) 0 (1- k))))))

(defthm cardano-vieta
  (implies (and (number-listp roots) (natp k) (<= k (len roots)))
           (equal (nth k (poly-from-roots roots))
                  (* (expt -1 (- (len roots) k))
                     (elem-sym (- (len roots) k) roots))))
  :hints (("Goal" :induct (cv-ind roots k)
                  :in-theory (disable mult-by-root mult-by-root-as-poly-add))))

;; ===========================================================================
;; PART III -- Equivalence of the two readings
;;             (paper's Section VI): the same table, read by grouping
;;             on the highest root index first (descending reading,
;;             a_n outermost: (poly-from-roots (rev roots))) or the
;;             lowest root index first (ascending reading, a_1
;;             outermost: (poly-from-roots roots)), gives the same
;;             coefficients.  This is exactly order-independence of the
;;             table construction: it does not matter whether the roots
;;             are multiplied in as given, or in reverse order.
;;             The two nested sum-product formulas themselves (paper's
;;             eqs. (6) and (7)) are defined and proved equal to the
;;             coefficients in poly-roots-nested-sums.lisp; arbitrary
;;             permutations of the roots are treated in
;;             poly-roots-permutations.lisp.
;; ===========================================================================

;; A plain textbook reverse, defined via append so that
;; (rev (cons x xs)) unfolds directly to (append (rev xs) (list x)).
(defun rev (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

;; Appending one more root at the END of the list and then building the
;; table has the same effect as building the table first and then
;; multiplying by that last root -- i.e. it does not matter whether a
;; root is the first one "peeled off" or the last one appended. This
;; follows directly from MULT-BY-ROOT-COMMUTES.
(defthm poly-from-roots-append-singleton
  (equal (poly-from-roots (append xs (list a)))
         (mult-by-root (poly-from-roots xs) a))
  :hints (("Goal"
           :induct (poly-from-roots xs)
           :in-theory (disable poly-add poly-scale poly-shift mult-by-root
                                mult-by-root-as-poly-add
                                (:definition poly-from-roots)))))

;; -----------------------------------------------------------------
;; THEOREM 3 (equivalence of the two readings; paper's Section VI):
;; the table construction does not depend on the order of the roots.
;; (poly-from-roots roots) multiplies the roots in from the last to the
;; first, so a1 is the outermost factor (ascending reading);
;; (poly-from-roots (rev roots)) multiplies them in from the first to the
;; last, as in Table III, so an is the outermost factor (descending
;; reading).  Both yield the identical coefficient list.
;; -----------------------------------------------------------------
(defthm poly-from-roots-reverse-invariant
  (equal (poly-from-roots (rev roots))
         (poly-from-roots roots))
  :hints (("Goal" :induct (poly-from-roots roots))))

;; Corollary, stated the way the paper states it (eq. (8)-(9)): the two
;; readings agree at every single coefficient, not just as whole lists.
(defthm reverse-order-construction-agrees-per-coefficient
  (equal (nth p (poly-from-roots (rev roots)))
         (nth p (poly-from-roots roots))))


;; ===========================================================================
;; PART III-B -- Guard verification
;;
;; Every function above carries a :guard; here they are all verified, in
;; dependency order. The recursive calls of POLY-FROM-ROOTS,
;; ELEM-SYM-LIST and ALTERNATE-SIGN pass their own results to
;; functions whose guard is NUMBER-LISTP, so each needs a lemma that the
;; result is itself a NUMBER-LISTP (the first is already above).
;; ===========================================================================

(defthm number-listp-elem-sym-list
  (number-listp (elem-sym-list roots)))

(defthm number-listp-negate-list
  (number-listp (negate-list lst)))

(defthm true-listp-rev
  (true-listp (rev x)))

(verify-guards number-listp)
(verify-guards poly-scale)
(verify-guards poly-neg)
(verify-guards poly-shift)
(verify-guards poly-add)
(verify-guards mult-by-root)
(verify-guards poly-eval)
(verify-guards triple-add-induct)
(verify-guards poly-from-roots)
(verify-guards prod-factors)
(verify-guards negate-list)
(verify-guards alternate-sign)
(verify-guards elem-sym)
(verify-guards elem-sym-list)
(verify-guards rev)

;; ===========================================================================
;; PART IV -- Ground numeric check (paper's Section VII-B):
;;            roots [3, -5, -11, -1], expect
;;            P(x) = x^4 + 14 x^3 + 20 x^2 - 158 x - 165
;;            i.e. coefficient list (-165 -158 20 14 1).
;;
;; assert-event just evaluates the ground (variable-free) claim and
;; fails the book's certification if it is not literally true -- no
;; proof search involved, this is a plain computation check.
;; ===========================================================================

(assert-event
 (equal (poly-from-roots '(3 -5 -11 -1))
        '(-165 -158 20 14 1)))

(assert-event
 (equal (poly-from-roots (rev '(3 -5 -11 -1)))
        '(-165 -158 20 14 1)))

(assert-event
 (equal (nth 2 (poly-from-roots '(3 -5 -11 -1)))
        20))

;; ===========================================================================
;; End of book.
;; ===========================================================================
