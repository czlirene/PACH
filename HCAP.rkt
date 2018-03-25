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
            (q undefined)]      ; can be undefined
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

    ; Update = Excp
    [Excp   (ex Perm Time Excp)
            (ex nil Time)]
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
    ; psa Clock QState 
    [REDState    (psa Clock AState RState CState TrnFn)]
)

; <------------------- SECURITY AUTOMATON GRAMMAR TEST CASES ------------------->
(define p0 (term (p 0)))
(define p1 (term (p 1)))
(define p2 (term (p 2)))
(define p3 (term (p 3)))

(define stat_p (term (,p0 ,p1)))
(define trns_p (term (,p2 ,p3)))
(define all_p  (term (,p0 ,p1 ,p2 ,p3)))

(define q_undefined (term (q undefined)))
(define q0 (term (q 0)))
(define q1 (term (q 1)))
(define q2 (term (q 2)))
(define all_q (term (,q0 ,q1 ,q2)))

; Stationary permission
(define stat_fn1 (term (,q0 ,p0 ,q0)))
(define stat_fn2 (term (,q1 ,p1 ,q1)))
; Transitioning permission 
; (define trn_fn1 (term (,q0 ,p2 ,q1)))
; (define trn_fn2 (term (,q1 ,p3 ,q2)))
; (define all_fn (term (,stat_fn1 ,stat_fn2 ,trn_fn1 ,trn_fn2)))

(define trn_fn1 (term (,q0 ,p1 ,q1)))
(define trn_fn2 (term (,q1 ,p2 ,q2)))
(define all_fn (term (,stat_fn1 ,trn_fn1 ,trn_fn2)))

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
    (test-equal (redex-match? HCAP P all_p) #true)

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
(define clo3 (term (clo 3)))
(define clo4 (term (clo 4)))

(define tas0 (term (tas 0)))
(define tas1 (term (tas 1)))
(define tas2 (term (tas 2)))
(define tas3 (term (tas 3)))

(define trs0 (term (trs 0)))
(define trs1 (term (trs 1)))
(define trs2 (term (trs 2)))

(define t0 (term (t 0)))
(define t1 (term (t 1)))
(define t2 (term (t 2)))

(define tser0 (term (tser 0)))
(define tser1 (term (tser 1)))
(define tser2 (term (tser 2)))

(define nil_t0_excp (term (ex nil ,t0)))           ; nil excp @ time 0
(define nil_t1_excp (term (ex nil ,t1)))           ; nil excp @ time 0
(define excp0 (term (ex ,p1 ,t1 ,nil_t0_excp)))
(define excp1 (term (ex ,p2 ,t2 ,excp0)))

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
(define as1 (term (,q0 ,tas2)))

(define rs0 (term (,trs1 ,nil_t0_excp)))        ; initial state of RS0

(define cs0 '())                                ; initial state of CS0 (empty list of tickets)
(define cs1 (term (,excp1 ,nil_t0_excp)))
(define cs2 (term (,excp1)))
(define cs3 (term (,nil_t1_excp)))

(define ps0 (term (ps ,clo2 ,as0 ,rs0 ,cs0)))           ; initial state of PS0
(define psa0 (term (psa ,clo2 ,as0 ,rs0 ,cs0 ,all_fn)))        ; Initial states: use this for testing for issue


;;; psa1 --(T-DRP)-->  psa2
(define psa1 (term (psa ,clo2 ,as0 ,rs0 ,cs1 ,all_fn)))
(define psa2 (term (psa ,clo3 ,as0 ,rs0 ,cs2 ,all_fn)))

;;; psa1 --T-UPD(nil)--> psa3
;;; (define psa1 (term (psa ,clo2 ,as0 ,rs0 ,cs3 ,all_fn)))
;;; (define psa3 (term (psa ,clo3 ,as1 ,rs0 ,cs3 ,all_fn)))



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

    ; Testing CS states
    (test-equal (redex-match? HCAP CState cs1) #true)

    ; Testing RED state
    (test-equal (redex-match? HCAP REDState psa0) #true)
    (test-equal (redex-match? HCAP REDState psa1) #true)
)

(define red
    (reduction-relation HCAP 
    ; TODO: T-ISS, auth server issues a cap to the client
    ; effect: t_clo +=1, C' = C + {cap (t_as, F(M_q_as))}
    ; (--> (psa (clo natural)                 AState RState CState_1 P Q initQ TrnFn)
    ;      (psa (clo ,(+ 1 (term natural)))   AState RState CState_2 P Q initQ TrnFn)
         
    ;      ; Get the q_as and t_as from AState
    ;      (where (Q_AS T_AS) AState)

    ;      ; insert new capability into CState_1 -> CState_2 
    ;      (where )

    ;      ; Give this transition a name
    ;      (computed-name (term (issue-cap (T_AS, ))))
    ; )

    ; TODO: T-REQS, the client requests to exercise a stat perm
    ; TODO: T-REQT, the client requests to exercise a tran perm
    ; T-FSH, garbage collection
    ; new(t_as) = new(t_rs) = t_clo,
    ; new(e_rs) = nil (t of the outermost e_rs)
    ; if t_as = first(e_rs) then new(q_as) = TrnFn*(q_as, e_rs)
    ;;; (--> (psa Clock_1 AState_1 RState_2 CState TrnFn)
    ;;;      (psa Clock_2 AState_2 RState_2 CState TrnFn)

    ;;;      ; increment clock 
    ;;;      (where Clock_2 ,(increment-clock (term Clock_1)))



    ;;; )

    ; T-UPD, client updates the internal state of auth server
    ; if Tic in C, and Tic = upd(e), and the first(e) = t_as (THE INNER MOST TIME)
    ; Then new(t_as) = t_clo, new(q_as) = TrnFn(q_as, e)

    ; CASE 1: upd(e) = (ex nil(t)), q_as stays the same regardless, t_as' = t_clo
    (--> (psa Clock_1 (QState TimeAS_1) RState CState TrnFn)
         (psa Clock_2 (QState TimeAS_2) RState CState TrnFn)

         ; increment clock 
         (where Clock_2 ,(increment-clock (term Clock_1)))

         ; Get the current tas
         (where (tas natural_1) TimeAS_1)

         ; find an upd(e) ticket in C where Time = TimeAS_1
         (where (Tic_1 ... (ex nil (t natural_1)) Tic_3 ...) CState)

         ; Get the current clock time
         (where (clo natural_2) Clock_1)

         ; Update the t'as = tclo
         (where TimeAS_2 (tas natural_2))

         (computed-name (term (update (ex nil (t TimeAS_1)))))

    )

    ; CASE 2: upd(e) = (ex Perm Time Excp)
    (--> (psa Clock_1 AState_1 RState CState TrnFn)
         (psa Clock_2 AState_2 RState CState TrnFn)

         ; increment clock 
         (where Clock_2 ,(increment-clock (term Clock_1)))

         ; find a upd(e) ticket in C
         (where (Tic_1 ... (ex Perm Time Excp) Tic_3 ...) CState) 

         ; update the AState
         (where AState_2 ,(recv-update-astate (term AState_1) (term Tic_2) (term Clock_1) (term TrnFn)))

         ; give this transition a name
         (computed-name (term (update Tic_2)))
    )

    ; TODO: T-RCV, client asks the resource server to recover a lost ticket

    ; T-DRP, the client accidentally drops some of its tickets [DONE]
    ; if Tic in C, then can be dropped
    (--> (psa Clock_1 AState RState CState_1 TrnFn)
         (psa Clock_2 AState RState CState_2 TrnFn)

         ; increment the clock
         (where Clock_2 ,(increment-clock (term Clock_1)))

         ; Find a ticket to drop 
         (where (Tic_1 ... Tic_2 Tic_3 ...) CState_1)

         ; Remove the ticket, and store into CState_2
         (where CState_2 ,(remove (term Tic_2) (term CState_1)))

         ; Give this transition a name
         (computed-name (term (drop Tic_2)))
    )
    )
)

; <------------------- BEGIN: RED Helpers ------------------->
; Increment global clock value, this will be called from all the trnx
(define (increment-clock clock)
    (let ([val (second clock)])
         (term (clo ,(+ 1 val)))
    )
)
(trace increment-clock)

; /******************** T-UPD(Tic) ********************/

; Case 2 Handler: Tic = (ex Perm Time Excp)
; Need to update both t_as, and q_as 
(define (recv-update-astate astate excp t_clo TrnFn)
    (if (eqv? (first excp) 'ex)
        (let ([q_as (first astate)]
              [t_as (second astate)]
              [time (third excp)])
            ; Check for precondition first(e) = t_as
            (if (is-texcp-eqv-tas? t_as (get-first-excp-time excp))
                (recv-compute-astate2 q_as excp t_clo TrnFn)           ; return new AState
                (term ,astate)                                         ; return old AState, no change
            )
        )
        (term ,astate)
    )
)

; Called from recv-update-astate
; Compute the new AState, with the updated TimeAS and QState
; return AState
(define (recv-compute-astate2 qstate excp t_clo TrnFn)
    (let ([newQAS (recv-compute-qas qstate excp TrnFn)]
          [newTAS (term (tas (second t_clo)))])
         (term (,newQAS ,newTAS))
    )
)

; Called from recv-compute-astate2
; Compute the new QState after applying all the permissions found in Exceptions
; return QState
(define (recv-compute-qas qstate excp TrnFn)
    (if (eqv? (second excp) 'nil)
        ; base case, we got to the first(e), return the current state
        (term ,qstate)
        ; otherwise, call apply-excp with the recursive call to self to determine the state
        (apply-excp (recv-compute-qas qstate (fourth excp) TrnFn) (second excp) TrnFn)
    )
)
; (trace recv-compute-qas)

; Called from recv-compute-qas 
; Apply the permission to the QState, if it is found in the TrnFn list
; return QState
(define (apply-excp qstate perm TrnFn)
    (if (null? TrnFn)                   ; if there are no fns, then return original state
        (term ,qstate)
        ; otherwise, find the (qstate perm) pair in TrnFn
        (let ([parFn (first TrnFn)])
            (let ([fn_q1 (first  parFn)]
                  [fn_p  (second parFn)]
                  [fn_q2 (third  parFn)])

                ; if the current ParFn has (qstate perm) as the first 2, return the last
                (if (and (eqv? fn_q1 qstate)
                         (eqv? fn_p  perm))
                    (term ,fn_q2)
                    ; otherwise, check the rest of the list of TrnFn
                    (apply-excp qstate perm (rest TrnFn))
                )
            )
        )
    )
)
; (trace apply-excp)

; Called from recv-update-tas       (case 1 handler)
;             recv-update-astate    (case 2 handler)
; param: t_as, and t_excp
; Determine if the time Ex(t) == t_as
; return boolean
(define (is-texcp-eqv-tas? t_as t_excp)
    (eqv? (second t_as) (second t_excp))
)
(trace is-texcp-eqv-tas?)

; Called from recv-update-tas       (case 1 handler)
;             recv-update-astate    (case 2 handler)
; Retrieve the first (aka the innermost) exception
; return Time
(define (get-first-excp-time excp)
    ; the innermost excp will always be of the form (ex nil Time)
    (if (eqv? (second excp) 'nil)
        (term (third excp))                 ; return the time
        (get-first-excp-time (fourth excp)) ; otherwise, keep going deeper
    )
)

(trace get-first-excp-time)

; /******************** END: T-UPD ********************/

; <------------------- BEGIN: INV-# ------------------->
; 1. Global clock is larger than all the timestamps within the protocol state
(define (inv-1? pstate)
    (let ([clock (second pstate)]
          [astate (third pstate)]
          [rstate (fourth pstate)]
          [cstate (fifth pstate)])
         (and 
            (is-clock-larger-tas? clock astate)
            (is-clock-larger-trs? clock rstate)
            (is-clock-larger-time? clock cstate)
         )
    )
)

; called from inv-1
; check if the global clock is larger than the time in auth server
(define (is-clock-larger-tas? clock astate)
    (let ([tas (second astate)])
         (> (second clock) (second tas))
    )
)

; called from inv-1
; check if the global clock is larger than the time in resrc server
(define (is-clock-larger-trs? clock rstate)
    (let ([trs (first rstate)])
         (> (second clock) (second trs))
    )
)

; called from inv-1
; check if global clock is larger than the time in all tickets in client
(define (is-clock-larger-time? clock cstate)
    (if (null? cstate)
        #true
        (let ([tic (first cstate)])
             (and 
                (is-clock-larger-tic? clock tic)
                (is-clock-larger-time? clock (rest cstate))
             )
        )
    )
)   

; called from is-clock-larger-time
; check what type of ticket it is, and call the appropriate predicate
(define (is-clock-larger-tic? clock tic)
    (if (eqv? (first tic) 'ex)
        (is-clock-larger-exp? clock tic)
        (is-clock-larger-cap? clock tic)
    )
)

; called from is-clock-larger-tic
; check if the clock is larger than the the time (t) in exceptions
(define (is-clock-larger-exp? clock exp)
    (let ([time (third exp)])
         (> (second clock) (second time))
    )
)

; called from is-clock-larger-tic
; check if the clock is larger than the the tser in capability
(define (is-clock-larger-cap? clock cap)
    (let ([tser (first cap)])
         (> (second clock) (second tser))
    )
)

(module+ test
    ;;; (test-->>E #:steps 1 red psa1 psa2)         ; testing T_DRP
    ;;; (test-->>E #:steps 1 red psa1 psa3)         ; testing T-UPD(nil)
)

(module+ test
  (test-results)
)
