#lang scheme
(require redex)
(require racket/trace)

(define-language HCAP
    ; There is only 1 resource server
    ; Definition of Security Automaton
    ; SA = {Permissions}, {States}, initState, TrnFn (Q x E ~> Q)
    [Perm   (p natural)]        ; one permission
    [P      (Perm ...)]         ; finite set of permissions (Perm)
    
    [QState (q natural)         ; 1 state in the set of Q
            (q undefined)]          ; can be undefined
    [Q      (QState ...)]       ; Finite set of automaton states (QState)

    [ParFn  (QState Perm QState)]    ; 1 partial transition f'n, where (Q P) -> undefined is possible
    [TrnFn  (ParFn ...)]         ; Set of all the partial transition functions stored in a SA (can be empty list)

    [SecA   (sa P Q QState TrnFn)] ; Security Automaton

    ; Definition of Protocol State
    ; PS = t_Clo, {AState}, {RState}, {CState}
    ; s.t   AState = (q_as, t_as)
    ;       RState = (t_rs, e_rs)
    ;       CState = {Tickets}
    ;       Tickets := (ex(p, t, e))
    ;               := (t_ser, F)

    [Clock  (clo natural)]          ; global clock value

    [AState (QState TimeAS)]        ; Authorization server state
    [TimeAS (tas natural)]

    [RState (TimeRS Excp)]          ; Excp here records past permissions 
    [TimeRS (trs natural)]

    [CState (Tic ...)]            ; finite set of tickets
    [Tic    Excp                    ; Upd = Excp
            Cap]

    ; Update
    [Excp   (ex Perm Time Excp)
            (nil Time)]
    [Time   (t natural)]            ; general time, used in exception

    ; Capability
    [Cap    (TimeSER Frag)]
    [TimeSER (tser natural)]        ; used for capability
    [Frag   (P TrnPs (Defs ...))]    ; Frag = {State Perms} {Trnx Perms} {Frag of any Trnx Perm State}
    
    [TrnP   (Perm QState)]
    [TrnPs  (TrnP ...)]
    
    [Defs   (P TrnPs)
            null]

    [PState (ps Clock AState RState CState)]    ; protocol state

    ; RED State: Combination of PState and SA
    [RED    (psa Clock AState RState CState P Q QState TrnFn)]
)


; <------------------- SECURITY AUTOMATON GRAMMAR TEST CASES ------------------->
(define p0 (term (p 0)))
(define p1 (term (p 1)))
(define p2 (term (p 2)))
(define p3 (term (p 3)))

(define stat_p (term (,p0 ,p1)))
(define trns_p (term (,p2 ,p3)))
(define all_p (term (,p0 ,p1 ,p2 ,p3)))

(define q_undefined (term (q undefined)))
(define q0 (term (q 0)))
(define q1 (term (q 1)))
(define q2 (term (q 2)))
(define all_q (term (,q0 ,q1 ,q2)))

; Stationary permission
(define stat_fn1 (term (,q0 ,p0 ,q0)))
(define stat_fn2 (term (,q1 ,p1 ,q1)))
; Transitioning permission 
(define trn_fn1 (term (,q0 ,p2 ,q1)))
(define trn_fn2 (term (,q1 ,p3 ,q2)))
(define all_fn (term (,stat_fn1 ,stat_fn2 ,trn_fn1 ,trn_fn2)))

(module+ test
    ; Testing singular permissions
    (test-equal (redex-match? HCAP Perm p0) #true)
    (test-equal (redex-match? HCAP Perm p1) #true)
    (test-equal (redex-match? HCAP Perm p2) #true)
    (test-equal (redex-match? HCAP Perm p3) #true)

    ; Testing list of permissions
    (test-equal (redex-match? HCAP P '()) #true)
    (test-equal (redex-match? HCAP P stat_p) #true)
    (test-equal (redex-match? HCAP P trns_p) #true)

    ; Testing singular qstates
    (test-equal (redex-match? HCAP QState q0) #true)
    (test-equal (redex-match? HCAP QState q1) #true)
    (test-equal (redex-match? HCAP QState q2) #true)
    (test-equal (redex-match? HCAP QState q_undefined) #true)

    ; Testing transition functions 
    ; Empty list
    (test-equal (redex-match? HCAP TrnFn '()) #true)
    ; Stationary
    (test-equal (redex-match? HCAP ParFn stat_fn1) #true)
    (test-equal (redex-match? HCAP ParFn stat_fn2) #true)
    ; Transition
    (test-equal (redex-match? HCAP ParFn trn_fn1) #true)
    (test-equal (redex-match? HCAP ParFn trn_fn2) #true)
)

; <------------------- PROTOCOL STATE GRAMMAR TEST CASES ------------------->
(define clo0 (term (clo 0)))
(define clo1 (term (clo 1)))
(define clo2 (term (clo 2)))

(define tas0 (term (tas 0)))
(define tas1 (term (tas 1)))
(define tas2 (term (tas 2)))

(define trs0 (term (trs 0)))
(define trs1 (term (trs 1)))
(define trs2 (term (trs 2)))

(define t0 (term (t 0)))
(define t1 (term (t 1)))
(define t2 (term (t 2)))

(define tser0 (term (tser 0)))
(define tser1 (term (tser 1)))
(define tser2 (term (tser 2)))

(define nil_t0_excp (term (nil ,t0)))           ; nil excp @ time 0
(define excp0 (term (ex ,p0 ,t1 ,nil_t0_excp)))
(define excp1 (term (ex ,p1 ,t2 ,excp0)))

(define trnp2 (term (,p2 ,q1)))
(define trnp3 (term (,p3 ,q2)))
(define trnps1 (term (,trnp2 ,trnp3)))

(define defs_null (term null))
(define defs_list (list (term ,defs_null)))

(define emptylist '())                          ; empty list
(define frag0 (term (,stat_p ,trnps1 ,defs_list)))
(define frag_no_statp (term (,emptylist ,trnps1 ,defs_list)))
(define frag_no_trnps (term (,stat_p ,emptylist ,defs_list)))
(define frag_no_defs (term (,stat_p ,trnps1 ,emptylist)))

(define cap0 (term (,tser0 ,frag0)))

(define as0 (term (,q0 ,tas1)))                 ; initial state of AS0
(define rs0 (term (,trs1 ,nil_t0_excp)))        ; initial state of RS0
(define cs0 '())                                ; initial state of CS0 (empty list of tickets)
(define ps0 (term (ps ,clo2 ,as0 ,rs0 ,cs0)))   ; initial state of PS0

(define psa0 (term (psa ,clo2 ,as0 ,rs0 ,cs0 ,all_p ,all_q ,q0 ,all_fn)))

(module+ test
    ; Testing all the times
    (test-equal (redex-match? HCAP Clock clo0) #true)
    (test-equal (redex-match? HCAP TimeAS tas0) #true)
    (test-equal (redex-match? HCAP TimeRS trs0) #true)
    (test-equal (redex-match? HCAP Time t0) #true)
    (test-equal (redex-match? HCAP TimeSER tser0) #true)

    ; Testing exception
    (test-equal (redex-match? HCAP Excp nil_t0_excp) #true)
    (test-equal (redex-match? HCAP Excp excp0) #true)
    (test-equal (redex-match? HCAP Excp excp1) #true)

    ; Testing transition permissions
    (test-equal (redex-match? HCAP TrnP trnp2) #true)
    (test-equal (redex-match? HCAP TrnP trnp3) #true)
    
    (test-equal (redex-match? HCAP TrnPs '()) #true)
    (test-equal (redex-match? HCAP TrnPs trnps1) #true)

    ; Testing fragments
    (test-equal (redex-match? HCAP Defs defs_null) #true)

    (test-equal (redex-match? HCAP Frag frag0) #true)
    (test-equal (redex-match? HCAP Frag frag_no_trnps) #true)
    (test-equal (redex-match? HCAP Frag frag_no_statp) #true)
    (test-equal (redex-match? HCAP Frag frag_no_defs) #true)

    (test-equal (redex-match? HCAP Cap cap0) #true)

    ; Testing AS, RS, CS, and PS initial State
    (test-equal (redex-match? HCAP AState as0) #true)
    (test-equal (redex-match? HCAP RState rs0) #true)
    (test-equal (redex-match? HCAP CState cs0) #true)
    (test-equal (redex-match? HCAP PState ps0) #true)

    ; Testing RED state
    (test-equal (redex-match? HCAP RED psa0) #true)
)
(module+ test
  (test-results)
)
