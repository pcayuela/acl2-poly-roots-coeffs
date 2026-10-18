;; ===========================================================================
;; poly-roots-nested-sums.lisp
;;
;; The two nested sum-product readings of the coefficients of
;;     P(s) = prod_{i=1}^n (s - a_i)
;; from the companion paper (Cayuela, "Calculo de los coeficientes de un
;; polinomio a partir de sus raices", eqs. (6) and (7)), formalized and
;; proved equal -- for every n and every p -- to the coefficients built by
;; POLY-FROM-ROOTS, and hence to each other.
;;
;;   eq. (6), descending reading ("hojas"):
;;     b_p = (-1)^(n-p) sum_{i_p=n-p}^{n} a_{i_p}
;;                      prod_{q=p+1}^{n-1} sum_{i_q=n-q}^{i_{q-1}-1} a_{i_q}
;;   eq. (7), ascending reading ("pizarron"):
;;     b_p = (-1)^(n-p) prod_{j=1}^{n-p} sum_{k_j=k_{j-1}+1}^{p+j} a_{k_j},
;;                      k_0 = 0
;;
;; Both are nested sums "sum over an index of a_index times the nested sum
;; of the next level".  The roots are a_i = (nth (i-1) roots).
;;
;;   DESC-SUM k i m a : sum_{i'=i}^{m} a_i' * DESC-SUM (k-1) (k-1) (i'-1) a
;;       the level with k roots still to choose; eq. (6) is
;;       (DESC-SUM (n-p) (n-p) n a)   [level q has k = n-q].
;;   ASC-SUM c k u a  : sum_{k'=k}^{u} a_k' * ASC-SUM (c-1) (k'+1) (u+1) a
;;       the level with c roots still to choose, index from k, bound u;
;;       eq. (7) is (ASC-SUM (n-p) 1 (p+1) a)   [k_0 = 0, level j bound p+j].
;;
;; Guards are not declared here (the book is about the logical statements).
;; ===========================================================================

(in-package "ACL2")
(include-book "poly-roots-coeffs")

(set-verify-guards-eagerness 0)

(defun ai (i a) (nth (+ -1 i) a))

(defun desc-sum (k i m a)
  (declare (xargs :measure (make-ord 1 (+ 1 (nfix k)) (nfix (- (+ 1 (nfix m)) (nfix i))))))
  (cond ((zp k) 1)
        ((or (not (natp i)) (not (natp m)) (< m i)) 0)
        (t (+ (* (ai i a) (desc-sum (- k 1) (- k 1) (- i 1) a))
              (desc-sum k (+ i 1) m a)))))

(defun asc-sum (c k u a)
  (declare (xargs :measure (make-ord 1 (+ 1 (nfix c)) (nfix (- (+ 1 (nfix u)) (nfix k))))))
  (cond ((zp c) 1)
        ((or (not (natp k)) (not (natp u)) (< u k)) 0)
        (t (+ (* (ai k a) (asc-sum (- c 1) (+ k 1) (+ u 1) a))
              (asc-sum c (+ k 1) u a)))))

;; ---------------------------------------------------------------------------
;; Facts about ELEM-SYM on prefixes and segments

(defthm elem-sym-append-last
  (implies (posp k)
           (equal (elem-sym k (append xs (list x)))
                  (+ (elem-sym k xs) (* x (elem-sym (1- k) xs)))))
  :hints (("Goal" :induct (elem-sym k xs))))

(defthm nthcdr-cons-form
  (implies (and (posp k) (<= k (len a)))
           (equal (nthcdr (+ -1 k) a)
                  (cons (nth (+ -1 k) a) (nthcdr k a)))))

(defthm len-take-nfix
  (equal (len (take n x)) (nfix n)))

(defthm elem-sym-take-short
  (implies (and (natp n) (< n c) (natp c))
           (equal (elem-sym c (take n x)) 0))
  :hints (("Goal" :use ((:instance elem-sym-zero-above-length (k c) (lst (take n x)))))))

(defthm take-peel-last
  (implies (and (posp m) (<= m (len a)))
           (equal (take m a)
                  (append (take (+ -1 m) a) (list (nth (+ -1 m) a)))))
  :rule-classes nil)

(defthm elem-sym-take-peel
  (implies (and (posp k) (posp m) (<= m (len a)))
           (equal (elem-sym k (take m a))
                  (+ (elem-sym k (take (+ -1 m) a))
                     (* (nth (+ -1 m) a) (elem-sym (+ -1 k) (take (+ -1 m) a))))))
  :hints (("Goal" :use (take-peel-last
                        (:instance elem-sym-append-last
                                   (xs (take (+ -1 m) a)) (x (nth (+ -1 m) a)))))))

;; ---------------------------------------------------------------------------
;; Ascending reading: the sum over increasing index chains is the
;; elementary symmetric function of the segment a_k ... a_(u+c-1).

(defthm asc-sum-is-elem-sym
  (implies (and (posp k) (natp u) (natp c) (<= (+ -1 u c) (len a)))
           (equal (asc-sum c k u a)
                  (elem-sym c (take (nfix (- (+ u c) k)) (nthcdr (+ -1 k) a)))))
  :hints (("Goal" :induct (asc-sum c k u a))))

;; ---------------------------------------------------------------------------
;; Descending reading: partial sums from i up to m differ from the
;; symmetric functions of the prefixes by the part below i.

(defthm desc-sum-diff
  (implies (and (posp k) (natp i) (<= k i) (natp m) (<= m (len a)))
           (equal (desc-sum k i m a)
                  (- (elem-sym k (take m a))
                     (elem-sym k (take (min (+ -1 i) m) a)))))
  :hints (("Goal" :induct (desc-sum k i m a))))

(defthm desc-sum-is-elem-sym
  (implies (and (natp k) (natp m) (<= m (len a)))
           (equal (desc-sum k k m a) (elem-sym k (take m a))))
  :hints (("Goal" :cases ((zp k)))))

;; ---------------------------------------------------------------------------
;; The two readings of the paper, equal to the table coefficients.

;; TAKE of the whole list
(defthm take-len-number-listp
  (implies (number-listp roots)
           (equal (take (len roots) roots) roots)))

(defthm eq6-descending-reading
  (implies (and (number-listp roots) (natp p) (<= p (len roots)))
           (equal (nth p (poly-from-roots roots))
                  (* (expt -1 (- (len roots) p))
                     (desc-sum (- (len roots) p) (- (len roots) p) (len roots) roots))))
  :hints (("Goal" :in-theory (disable desc-sum desc-sum-diff elem-sym-take-peel)
                  :use (cardano-vieta
                        (:instance desc-sum-is-elem-sym
                                   (k (- (len roots) p)) (m (len roots)) (a roots))))))

(defthm eq7-ascending-reading
  (implies (and (number-listp roots) (natp p) (<= p (len roots)))
           (equal (nth p (poly-from-roots roots))
                  (* (expt -1 (- (len roots) p))
                     (asc-sum (- (len roots) p) 1 (+ p 1) roots))))
  :hints (("Goal" :in-theory (disable asc-sum asc-sum-is-elem-sym elem-sym-take-peel)
                  :use (cardano-vieta
                        (:instance asc-sum-is-elem-sym
                                   (k 1) (u (+ p 1)) (c (- (len roots) p)) (a roots))))))

(defthm eq8-readings-agree
  (implies (and (number-listp roots) (natp p) (<= p (len roots)))
           (equal (desc-sum (- (len roots) p) (- (len roots) p) (len roots) roots)
                  (asc-sum (- (len roots) p) 1 (+ p 1) roots)))
  :hints (("Goal" :use ((:instance eq6-descending-reading)
                        (:instance eq7-ascending-reading))
                  :in-theory (disable eq6-descending-reading eq7-ascending-reading))))

;; Ground checks on the example of the paper, roots (3 -5 -11 -1):
;; b_2 = 20, b_0 = -165.
(assert-event (equal (* (expt -1 2) (desc-sum 2 2 4 '(3 -5 -11 -1))) 20))
(assert-event (equal (* (expt -1 2) (asc-sum 2 1 3 '(3 -5 -11 -1))) 20))
(assert-event (equal (* (expt -1 4) (desc-sum 4 4 4 '(3 -5 -11 -1))) -165))
(assert-event (equal (* (expt -1 4) (asc-sum 4 1 1 '(3 -5 -11 -1))) -165))
