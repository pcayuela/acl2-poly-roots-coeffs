;; ===========================================================================
;; poly-roots-nested-chains.lisp
;;
;; Term-by-term structure of the two nested-sum readings of
;; poly-roots-nested-sums.lisp (paper's eqs. (6) and (7)).  With
;; m = n - p, both readings are
;;
;;   descending:  b_p = (-1)^m prod_{j=1}^m sum_{i_j = m-j+1}^{i_(j-1) - 1} a_{i_j},  i_0 = n+1
;;   ascending:   b_p = (-1)^m prod_{j=1}^m sum_{i_j = i_(j-1) + 1}^{n-m+j} a_{i_j},  i_0 = 0
;;
;; Each summand is the product of the roots picked by one chain of
;; indices (i_1 ... i_m).  poly-roots-nested-sums.lisp proves that both
;; readings have the same VALUE.  This book makes the chains explicit
;; and proves, for every n and p:
;;
;;   - each reading is the sum, over its chains, of the product of the
;;     roots the chain picks (DESC-SUM-IS-SUM-OVER-CHAINS,
;;     ASC-SUM-IS-SUM-OVER-CHAINS);
;;   - the mirror i -> n+1-i maps the chains of the descending reading
;;     exactly onto those of the ascending reading, in reverse order
;;     (READINGS-ARE-MIRROR-IMAGES): one reading is the other, term by
;;     term, on the reversed roots;
;;   - each reading has C(n,m) chains, Pascal's triangle
;;     (NUMBER-OF-TERMS-ASCENDING, NUMBER-OF-TERMS-DESCENDING), and no
;;     chain is repeated (NO-DUPLICATE-TERMS-ASCENDING,
;;     NO-DUPLICATE-TERMS-DESCENDING);
;;   - the chains of each reading are exactly the strictly monotone
;;     chains of m indices from 1..n, increasing or decreasing
;;     (ASCENDING-TERMS-ARE-ALL-INCREASING-CHAINS,
;;     DESCENDING-TERMS-ARE-ALL-DECREASING-CHAINS): every set of m
;;     distinct roots appears in each reading, exactly once.
;;
;; Guards are not declared here (the book is about the logical statements).
;; ===========================================================================

(in-package "ACL2")
(include-book "poly-roots-nested-sums")

(set-verify-guards-eagerness 0)

;; ---------------------------------------------------------------------------
;; The chains of each reading, enumerated with the same recursion as
;; DESC-SUM and ASC-SUM.

(defun cons-each (x l)
  (if (atom l) nil (cons (cons x (car l)) (cons-each x (cdr l)))))

(defun desc-ch (k i m)
  (declare (xargs :measure (make-ord 1 (+ 1 (nfix k)) (nfix (- (+ 1 (nfix m)) (nfix i))))))
  (cond ((zp k) (list nil))
        ((or (not (natp i)) (not (natp m)) (< m i)) nil)
        (t (append (cons-each i (desc-ch (- k 1) (- k 1) (- i 1)))
                   (desc-ch k (+ i 1) m)))))

(defun asc-ch (c k u)
  (declare (xargs :measure (make-ord 1 (+ 1 (nfix c)) (nfix (- (+ 1 (nfix u)) (nfix k))))))
  (cond ((zp c) (list nil))
        ((or (not (natp k)) (not (natp u)) (< u k)) nil)
        (t (append (cons-each k (asc-ch (- c 1) (+ k 1) (+ u 1)))
                   (asc-ch c (+ k 1) u)))))

;; The product of the roots picked by a chain, and the sum over a list
;; of chains.
(defun prod-chain (ch a)
  (if (atom ch) 1 (* (ai (car ch) a) (prod-chain (cdr ch) a))))

(defun sum-prods (chs a)
  (if (atom chs) 0 (+ (prod-chain (car chs) a) (sum-prods (cdr chs) a))))

(defthm sum-prods-append
  (equal (sum-prods (append x y) a) (+ (sum-prods x a) (sum-prods y a))))

(defthm sum-prods-cons-each
  (equal (sum-prods (cons-each i l) a) (* (ai i a) (sum-prods l a))))

(in-theory (disable ai))

;; Each reading is the sum over its chains.
(defthm desc-sum-is-sum-over-chains
  (equal (desc-sum k i m a) (sum-prods (desc-ch k i m) a))
  :hints (("Goal" :induct (desc-sum k i m a))))

(defthm asc-sum-is-sum-over-chains
  (equal (asc-sum c k u a) (sum-prods (asc-ch c k u) a))
  :hints (("Goal" :induct (asc-sum c k u a))))

;; ---------------------------------------------------------------------------
;; Increasing chains in a window [lo, hi], in lexicographic order, and
;; the part of them whose first index lies in [lo, f].

(defun inc-ch (k lo hi)
  (declare (xargs :measure (make-ord 1 (+ 1 (nfix k)) (nfix (- (+ 1 (nfix hi)) (nfix lo))))))
  (cond ((zp k) (list nil))
        ((or (not (natp lo)) (not (natp hi)) (< hi lo)) nil)
        (t (append (cons-each lo (inc-ch (- k 1) (+ lo 1) hi))
                   (inc-ch k (+ lo 1) hi)))))

(defun incp (k lo f hi)
  (declare (xargs :measure (nfix (- (+ 1 (nfix f)) (nfix lo)))))
  (cond ((or (not (natp lo)) (not (natp f)) (< f lo)) nil)
        (t (append (cons-each lo (inc-ch (- k 1) (+ lo 1) hi))
                   (incp k (+ lo 1) f hi)))))

;; The mirror i -> n - i of a chain and of a list of chains.
(defun mirror-chain (n ch)
  (if (atom ch) nil (cons (- n (car ch)) (mirror-chain n (cdr ch)))))

(defun mirror-chains (n l)
  (if (atom l) nil (cons (mirror-chain n (car l)) (mirror-chains n (cdr l)))))

(defthm inc-ch-small
  (implies (and (posp k) (natp lo) (integerp hi) (< (+ hi 1) (+ lo k)))
           (equal (inc-ch k lo hi) nil))
  :hints (("Goal" :induct (inc-ch k lo hi))))

;; The ascending reading enumerates exactly the increasing chains in [k, u+c-1].
(defthm asc-ch-is-inc-ch
  (implies (and (natp c) (natp k) (natp u))
           (equal (asc-ch c k u) (inc-ch c k (+ u c -1))))
  :hints (("Goal" :induct (asc-ch c k u))))

(defthm incp-full
  (implies (and (posp k) (natp lo) (natp f) (natp hi) (<= f hi) (<= (+ hi 1) (+ f k)))
           (equal (incp k lo f hi) (inc-ch k lo hi)))
  :hints (("Goal" :induct (inc-ch k lo hi))))

(defthm incp-snoc
  (implies (and (natp lo) (natp f) (<= lo f))
           (equal (incp k lo f hi)
                  (append (incp k lo (- f 1) hi)
                          (cons-each f (inc-ch (- k 1) (+ f 1) hi)))))
  :hints (("Goal" :induct (incp k lo f hi))))

(defthm rev-append-x
  (equal (rev (append x y)) (append (rev y) (rev x))))

(defthm cons-each-append
  (equal (cons-each f (append x y)) (append (cons-each f x) (cons-each f y))))

(defthm rev-cons-each
  (equal (rev (cons-each f l)) (cons-each f (rev l))))

(defthm mirror-chains-append
  (equal (mirror-chains n (append x y)) (append (mirror-chains n x) (mirror-chains n y))))

(defthm mirror-chains-cons-each
  (equal (mirror-chains n (cons-each i l)) (cons-each (- n i) (mirror-chains n l))))

;; INCP enumerated from its last first index downwards, the order that
;; matches the mirror of DESC-CH.
(defun incd (k lo f hi)
  (declare (xargs :measure (nfix (+ 1 (- (ifix f) (nfix lo))))))
  (cond ((or (not (natp lo)) (not (integerp f)) (< f lo)) nil)
        (t (append (incd k lo (- f 1) hi)
                   (cons-each f (inc-ch (- k 1) (+ f 1) hi))))))

(defthm incd-is-incp
  (implies (natp lo) (equal (incd k lo f hi) (incp k lo f hi)))
  :hints (("Goal" :induct (incd k lo f hi))
          ("Subgoal *1/2" :use (:instance incp-snoc))))

(defthm desc-ch-zero (implies (zp k) (equal (desc-ch k i m) (list nil))))

(defthm desc-ch-empty (implies (and (not (zp k)) (< m i)) (equal (desc-ch k i m) nil)))

(defthm desc-ch-step
  (implies (and (not (zp k)) (natp i) (natp m) (<= i m))
           (equal (desc-ch k i m)
                  (append (cons-each i (desc-ch (- k 1) (- k 1) (- i 1)))
                          (desc-ch k (+ i 1) m)))))

(defthm inc-ch-zero (implies (zp k) (equal (inc-ch k lo hi) (list nil))))

(defthm incd-empty (implies (< f lo) (equal (incd k lo f hi) nil)))

(defthm incd-step
  (implies (and (natp lo) (integerp f) (<= lo f))
           (equal (incd k lo f hi)
                  (append (incd k lo (- f 1) hi)
                          (cons-each f (inc-ch (- k 1) (+ f 1) hi))))))

(defthm incd-full
  (implies (and (posp k) (natp lo) (natp f) (natp hi) (<= f hi) (<= (+ hi 1) (+ f k)))
           (equal (incd k lo f hi) (inc-ch k lo hi))))

(in-theory (disable (:definition desc-ch) (:definition inc-ch) (:definition incd)
                    incd-is-incp))

;; The mirror of the descending chains is the reverse of a block of
;; increasing chains.
(defthm mirror-desc-ch
  (implies (and (posp k) (natp s) (natp i) (natp nn) (< i nn) (<= k s))
           (equal (mirror-chains nn (desc-ch k s i))
                  (rev (incd k (- nn i) (- nn s) (- nn 1)))))
  :hints (("Goal" :induct (desc-ch k s i))
          ("Subgoal *1/3" :use ((:instance incd-full (k (- k 1)) (lo (+ 1 (- nn s)))
                                           (f (+ 1 (- nn k))) (hi (- nn 1)))))))

;; ---------------------------------------------------------------------------
;; MAIN THEOREM: the mirror i -> n+1-i maps the chains of the descending
;; reading of b_p exactly onto the chains of the ascending reading, in
;; reverse order.

(defthm readings-are-mirror-images
  (implies (and (natp p) (natp n) (<= p n))
           (equal (mirror-chains (+ n 1) (desc-ch (- n p) (- n p) n))
                  (rev (asc-ch (- n p) 1 (+ p 1)))))
  :hints (("Goal" :cases ((equal p n)))
          ("Subgoal 2" :use ((:instance mirror-desc-ch (k (- n p)) (s (- n p)) (i n) (nn (+ n 1)))
                             (:instance incd-full (k (- n p)) (lo 1) (f (+ p 1)) (hi n))))))

;; ---------------------------------------------------------------------------
;; Number of terms: C(n, m), Pascal's triangle.

(defun choose (n k)
  (cond ((zp k) 1)
        ((zp n) 0)
        (t (+ (choose (- n 1) (- k 1)) (choose (- n 1) k)))))

(defthm len-cons-each (equal (len (cons-each x l)) (len l)))

(defthm len-inc-ch
  (implies (and (natp lo) (integerp hi))
           (equal (len (inc-ch k lo hi)) (choose (nfix (- (+ hi 1) lo)) k)))
  :hints (("Goal" :induct (inc-ch k lo hi) :in-theory (enable inc-ch))))

(defthm len-mirror-chains (equal (len (mirror-chains n l)) (len l)))

(defthm len-rev-x (equal (len (rev x)) (len x)))

(defthm number-of-terms-ascending
  (implies (and (natp p) (natp n) (<= p n))
           (equal (len (asc-ch (- n p) 1 (+ p 1))) (choose n (- n p)))))

(defthm number-of-terms-descending
  (implies (and (natp p) (natp n) (<= p n))
           (equal (len (desc-ch (- n p) (- n p) n)) (choose n (- n p))))
  :hints (("Goal" :use ((:instance readings-are-mirror-images)
                        (:instance len-mirror-chains (n (+ n 1)) (l (desc-ch (- n p) (- n p) n))))
                  :in-theory (disable readings-are-mirror-images len-mirror-chains))))

;; ---------------------------------------------------------------------------
;; No chain is repeated.

(defthm member-cons-each-car
  (implies (member-equal ch (cons-each x l)) (equal (car ch) x)))

(defthm member-inc-ch-car
  (implies (and (member-equal ch (inc-ch k lo hi)) (not (zp k)))
           (and (consp ch) (<= lo (car ch))))
  :hints (("Goal" :induct (inc-ch k lo hi) :in-theory (enable inc-ch)))
  :rule-classes nil)

(defthm member-cons-each-cdr
  (iff (member-equal ch (cons-each x l))
       (and (consp ch) (equal (car ch) x) (member-equal (cdr ch) l))))

(defthm no-dup-cons-each
  (equal (no-duplicatesp-equal (cons-each x l)) (no-duplicatesp-equal l)))

(defthm member-append-x
  (iff (member-equal a (append x y)) (or (member-equal a x) (member-equal a y))))

(defun disjoint-lists (x y)
  (if (atom x) t (and (not (member-equal (car x) y)) (disjoint-lists (cdr x) y))))

(defthm no-dup-append
  (equal (no-duplicatesp-equal (append x y))
         (and (no-duplicatesp-equal x) (no-duplicatesp-equal y) (disjoint-lists x y))))

(defthm disjoint-cons-each-inc-ch
  (implies (natp lo)
           (disjoint-lists (cons-each lo l) (inc-ch k (+ lo 1) hi)))
  :hints (("Subgoal *1/2" :use (:instance member-inc-ch-car (ch (cons lo (car l))) (lo (+ lo 1))))))

(defthm no-dup-inc-ch
  (no-duplicatesp-equal (inc-ch k lo hi))
  :hints (("Goal" :induct (inc-ch k lo hi) :in-theory (enable inc-ch))))

(defthm no-duplicate-terms-ascending
  (implies (and (natp p) (natp n) (<= p n))
           (no-duplicatesp-equal (asc-ch (- n p) 1 (+ p 1)))))

(defthm member-rev-x (iff (member-equal a (rev x)) (member-equal a x)))

(defthm disjoint-lists-singleton
  (equal (disjoint-lists x (list a)) (not (member-equal a x))))

(defthm no-dup-rev-x (equal (no-duplicatesp-equal (rev x)) (no-duplicatesp-equal x))
  :hints (("Goal" :induct (rev x))))

(defthm member-mirror-chains
  (implies (member-equal ch l) (member-equal (mirror-chain n ch) (mirror-chains n l))))

(defthm no-dup-mirror-chains
  (implies (no-duplicatesp-equal (mirror-chains n l)) (no-duplicatesp-equal l)))

(defthm no-duplicate-terms-descending
  (implies (and (natp p) (natp n) (<= p n))
           (no-duplicatesp-equal (desc-ch (- n p) (- n p) n)))
  :hints (("Goal" :use ((:instance readings-are-mirror-images)
                        (:instance no-dup-mirror-chains (n (+ n 1)) (l (desc-ch (- n p) (- n p) n))))
                  :in-theory (disable readings-are-mirror-images no-dup-mirror-chains))))

;; ---------------------------------------------------------------------------
;; Which chains: each reading enumerates EXACTLY the strictly monotone
;; chains of m distinct indices from 1..n (increasing for the ascending
;; reading, decreasing for the descending one).  Together with the
;; no-repetition theorems above, every set of m distinct roots appears in
;; each reading exactly once.

;; A strictly increasing chain of naturals within [lo, hi].
(defun inc-chainp (ch lo hi)
  (if (atom ch)
      (null ch)
    (and (natp (car ch)) (<= lo (car ch)) (<= (car ch) hi)
         (inc-chainp (cdr ch) (+ 1 (car ch)) hi))))

(defthm inc-chainp-weaken
  (implies (and (inc-chainp ch (+ 1 lo) hi) (integerp lo))
           (inc-chainp ch lo hi)))

(defun inc-ch-ind (k lo hi ch)
  (declare (xargs :measure (make-ord 1 (+ 1 (nfix k)) (nfix (- (+ 1 (nfix hi)) (nfix lo))))))
  (cond ((zp k) ch)
        ((or (not (natp lo)) (not (natp hi)) (< hi lo)) ch)
        (t (list (inc-ch-ind (- k 1) (+ lo 1) hi (cdr ch))
                 (inc-ch-ind k (+ lo 1) hi ch)))))

(defthm inc-ch-members
  (implies (and (natp lo) (natp hi) (natp k))
           (iff (member-equal ch (inc-ch k lo hi))
                (and (inc-chainp ch lo hi) (equal (len ch) k))))
  :hints (("Goal" :induct (inc-ch-ind k lo hi ch) :in-theory (enable inc-ch))))

;; A strictly decreasing chain of positive integers, the first one <= hi.
(defun dec-chainp (ch hi)
  (if (atom ch)
      (null ch)
    (and (posp (car ch)) (<= (car ch) hi)
         (dec-chainp (cdr ch) (- (car ch) 1)))))

(defthm dec-chainp-len-bound
  (implies (and (dec-chainp ch hi) (< 0 (len ch)))
           (<= (len ch) (car ch)))
  :rule-classes :linear)

(defthm dec-chainp-cdr
  (implies (and (dec-chainp ch hi) (consp ch))
           (dec-chainp (cdr ch) (- (car ch) 1)))
  :rule-classes :forward-chaining)

(defthm dec-chainp-weaken
  (implies (and (dec-chainp ch hi) (<= hi hi2))
           (dec-chainp ch hi2)))

(defun desc-ch-ind (k i m ch)
  (declare (xargs :measure (make-ord 1 (+ 1 (nfix k)) (nfix (- (+ 1 (nfix m)) (nfix i))))))
  (cond ((zp k) ch)
        ((or (not (natp i)) (not (natp m)) (< m i)) ch)
        (t (list (desc-ch-ind (- k 1) (- k 1) (- i 1) (cdr ch))
                 (desc-ch-ind k (+ i 1) m ch)))))

(defthm desc-ch-members
  (implies (and (natp k) (natp s) (natp i) (<= k s))
           (iff (member-equal ch (desc-ch k s i))
                (and (dec-chainp ch i) (equal (len ch) k)
                     (or (zp k) (<= s (car ch))))))
  :hints (("Goal" :induct (desc-ch-ind k s i ch)
                  :in-theory (disable desc-ch-step))
          ("Subgoal *1/3" :use (:instance desc-ch-step (i s) (m i)))))

;; The chains of the ascending reading of b_p are exactly the strictly
;; increasing chains of m = n-p indices from 1..n ...
(defthm ascending-terms-are-all-increasing-chains
  (implies (and (natp p) (natp n) (<= p n))
           (iff (member-equal ch (asc-ch (- n p) 1 (+ p 1)))
                (and (inc-chainp ch 1 n) (equal (len ch) (- n p))))))

;; ... and those of the descending reading are exactly the strictly
;; decreasing ones.
(defthm descending-terms-are-all-decreasing-chains
  (implies (and (natp p) (natp n) (<= p n))
           (iff (member-equal ch (desc-ch (- n p) (- n p) n))
                (and (dec-chainp ch n) (equal (len ch) (- n p))))))

;; ---------------------------------------------------------------------------
;; Ground check: n = 4, p = 2 (m = 2).
(assert-event (equal (desc-ch 2 2 4) '((2 1) (3 1) (3 2) (4 1) (4 2) (4 3))))
(assert-event (equal (asc-ch 2 1 3) '((1 2) (1 3) (1 4) (2 3) (2 4) (3 4))))
(assert-event (equal (mirror-chains 5 (desc-ch 2 2 4)) (rev (asc-ch 2 1 3))))
