

;(set-option :print-success true) 
;(set-option :produce-unsat-cores true)
;(set-option :produce-models true)
;(set-option :produce-proofs true)

;(echo "starting Z3...")


(declare-const n Int)
(declare-const k Int)
(declare-const node_number Int)
(declare-const disk_per_host Int)
(declare-const disk_raw_size Int)
(declare-const total_raw_space Int)
(declare-const min_node_number Int)
(declare-const replication_factor Real)
(declare-const total_max_effective_space Real)
(declare-const max_usage Real)
(declare-const required_space Int)

(assert (>= n 1))
(assert (<= n 8))
(assert (>= k 2))
(assert (<= k 4))

(assert (= replication_factor (/ (to_real (+ n k)) (to_real n))))



(assert (= disk_per_host 24))
(assert (= disk_raw_size (* 10 1000 1000 1000 1000))) ; 10 Tb
(assert (= total_raw_space (* disk_raw_size disk_per_host node_number)))

(assert (= required_space (* 10 1024 1024 1024 1024 1024))) ; 10 PiB

(assert (= min_node_number (+ n k 2)))
(assert (>= node_number min_node_number))

(assert (= total_max_effective_space  (* (to_real total_raw_space) 0.9 (/ 1.0 replication_factor))))
;(assert (= max_usage (* 0.85 (/ (to_real (- node_number 1)) (to_real node_number)))))
(assert (= max_usage 0.7))


(assert (<= (to_real required_space) (* total_max_effective_space max_usage)))





(check-sat)
(get-model)



