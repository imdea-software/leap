
(define-sort Addr () Int)
(declare-const null Addr)
(assert (= null 0))
(declare-const max_address Int)
(assert (= max_address 8))

(define-fun is_addr ((a Addr)) Bool
  (and (<= 0 a) (<= a 8)))
(define-sort Set () (_ BitVec 9))

(declare-const empty Set)
(assert (= empty (_ bv0 9)))

(define-fun singleton ((a Addr)) Set
  (ite (= a 1) #b000000010
  (ite (= a 2) #b000000100
  (ite (= a 3) #b000001000
  (ite (= a 4) #b000010000
  (ite (= a 5) #b000100000
  (ite (= a 6) #b001000000
  (ite (= a 7) #b010000000
  #b000000001))))))))

(define-fun setunion ((s Set) (r Set)) Set
  (bvor s r))

(define-fun intersection ((s Set) (r Set)) Set
  (bvand s r))

(define-fun setdiff ((s Set) (r Set)) Set
  (bvand s (bvnot r)))

(define-fun subseteq ((s1 Set) (s2 Set)) Bool
  (= s1 (bvand s1 s2)))

(define-fun in_set ((a Addr) (s Set)) Bool
  (not (= empty (intersection (singleton a) s))))

(assert (not (= empty (singleton null))))
(check-sat)
