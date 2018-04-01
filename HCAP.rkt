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
            (q unknown)]      ; can be undefined
    [Q      (QState ...)]       ; Finite set of automaton states (QState)

    [ParFn  (QState Perm QState)]    ; 1 partial transition f'n, where (Q P) -> undefined is possible
    [TrnFn  (ParFn ...)]         ; Set of all the partial transition functions stored in a SA (can be empty list)

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
    ; fragment will define 2 things:
    ;;; 1: The current state's set of permissions and their resulting state (Q1 P Q2)
    ;;; 2: Based on all transitioning permissions from 1, for all Q2, list all (Q2 P Q3) 
    [Frag   (TrnFn TrnFn)
            unknown
            undefined]         ; Frag = {Current frag allowed permissions} {The permissions allowed to be performed based on the states in current }
    
    ;;; [TrnP   (Perm QState)]
    ;;; [TrnPs  (TrnP ...)]
    ;;; [Defs   (Def ...)]
    ;;; [Def    (QState P TrnPs)]       ; the possible permissions that comes out of the TRNXPERMS in Frag, sorted by end qstate

    ;;; [PState (ps Clock AState RState CState)]    ; protocol state

    ; RED State: Combination of PState and SA
    [REDState    (psa Clock AState RState CState TrnFn)]
)

; <------------------- SECURITY AUTOMATON GRAMMAR TEST CASES ------------------->
; Perm, giving them names
(define p0 (term (p 0)))
(define p1 (term (p 1)))
(define p2 (term (p 2)))
(define p3 (term (p 3)))
(define p4 (term (p 4)))

; P, combining all the Perm into a list
(define perm_list (term (,p0 ,p1 ,p2 ,p3)))

(define stat_perms (term (,p1)))                ; list of all the stationary permissions
(define tran_perms (term (,p0 ,p2 ,p3 ,p4)))    ; list of all the transitioning permissions

; QState, giving them names
(define q_unknown (term (q unknown)))
(define q0 (term (q 0)))
(define q1 (term (q 1)))
(define q2 (term (q 2)))
(define q3 (term (q 3)))

; Q, combining all the QState into a list
(define qstate_list (term (,q_unknown ,q0 ,q1 ,q2 ,q3)))

; ParFn, by which permission does a state stay stationary, or transitions to another state
(define par_fn1 (term (,q0 ,p0 ,q1)))       ;q0 -> q1 when p0
(define par_fn2 (term (,q1 ,p1 ,q1)))       ;q1 <> q1 when p1       (stationary)
(define par_fn3 (term (,q1 ,p2 ,q2)))       ;q1 -> q2 when p2
(define par_fn4 (term (,q2 ,p3 ,q3)))       ;q2 -> q3 when p3
(define par_fn5 (term (,q3 ,p1 ,q3)))

(define par_fn0 (term (,q1 ,p4 ,q_unknown)))

; TrnFn, the list of all the functions defined in the security automaton
(define trn_fns (term (,par_fn1 ,par_fn2 ,par_fn3 ,par_fn4 ,par_fn0)))

(define stat_par_fns (term (,par_fn2)))                         ; list of stationary partial functions
(define tran_par_fns (term (,par_fn1 ,par_fn3 ,par_fn4)))       ; list of transitioning partial functions

(module+ test
    ; Testing singular permissions
    (test-equal (redex-match? HCAP Perm p0) #true)
    (test-equal (redex-match? HCAP Perm p1) #true)
    (test-equal (redex-match? HCAP Perm p2) #true)
    (test-equal (redex-match? HCAP Perm p3) #true)
    (test-equal (redex-match? HCAP Perm p4) #true)

    ; Testing permissions lists
    (test-equal (redex-match? HCAP P '()) #true)
    (test-equal (redex-match? HCAP P perm_list) #true)
    (test-equal (redex-match? HCAP P stat_perms) #true)
    (test-equal (redex-match? HCAP P tran_perms) #true)

    ; Testing singular qstates
    (test-equal (redex-match? HCAP QState q_unknown) #true)
    (test-equal (redex-match? HCAP QState q0) #true)
    (test-equal (redex-match? HCAP QState q1) #true)
    (test-equal (redex-match? HCAP QState q2) #true)
    (test-equal (redex-match? HCAP QState q3) #true)

    ; Testing qstate lists
    (test-equal (redex-match? HCAP Q '()) #true)
    (test-equal (redex-match? HCAP Q qstate_list) #true)

    ; Testing partial functions
    (test-equal (redex-match? HCAP ParFn par_fn0) #true)
    (test-equal (redex-match? HCAP ParFn par_fn1) #true)
    (test-equal (redex-match? HCAP ParFn par_fn2) #true)
    (test-equal (redex-match? HCAP ParFn par_fn3) #true)
    (test-equal (redex-match? HCAP ParFn par_fn4) #true)

    ; Testing list of partial functions
    (test-equal (redex-match? HCAP TrnFn '()) #true)
    (test-equal (redex-match? HCAP TrnFn trn_fns) #true)
    (test-equal (redex-match? HCAP TrnFn stat_par_fns) #true)
    (test-equal (redex-match? HCAP TrnFn tran_par_fns) #true)
)

; <------------------- PROTOCOL STATE GRAMMAR TEST CASES ------------------->
; Global clock values
(define clo0 (term (clo 0)))
(define clo1 (term (clo 1)))
(define clo2 (term (clo 2)))
(define clo3 (term (clo 3)))
(define clo4 (term (clo 4)))
(define clo5 (term (clo 5)))

; Authorization Server time values
(define tas0 (term (tas 0)))
(define tas1 (term (tas 1)))
(define tas2 (term (tas 2)))
(define tas3 (term (tas 3)))

; Resource server time values
(define trs0 (term (trs 0)))
(define trs1 (term (trs 1)))
(define trs2 (term (trs 2)))
(define trs3 (term (trs 3)))

; Exception time values
(define t0 (term (t 0)))
(define t1 (term (t 1)))
(define t2 (term (t 2)))
(define t3 (term (t 3)))

; Capability time values
(define tser0 (term (tser 0)))
(define tser1 (term (tser 1)))
(define tser2 (term (tser 2)))
(define tser3 (term (tser 3)))

; Authorization Server State 
(define as0 (term (,q0 ,tas1)))                 ; Initial state, A0 = (q0, 1)
(define as1 (term (,q0 ,tas2)))
(define as2 (term (,q1 ,tas3)))
(define as3 (term (,q0 ,tas3)))

; Exception (ex Perm Time Excp) or (ex nil Time)
(define excp_nil_0 (term (ex nil ,t0)))         ; Initial exception, nil(0)
(define excp_nil_1 (term (ex nil ,t1)))

(define excp0 (term (ex ,p0 ,t1 ,excp_nil_0)))  ; (Perm 0, Time 1, nil Time 0)
(define excp1 (term (ex ,p1 ,t2 ,excp0)))
(define excp2 (term (ex ,p0 ,t2 ,excp_nil_1))) 

; Resource server state (TimeRS, Excp)
(define rs0 (term (,trs1 ,excp_nil_0)))         ; Initial state, R0 = (1, nil(0))
(define rs1 (term (,trs2 ,excp1)))
(define rs2 (term (,trs2 ,excp2)))

; Frag (TrnFn TrnFn)
(define frag_undefined (term undefined))        ; Undefined ...
(define frag_unknown (term unknown))            ; Happens when exercising TrnP to a (q unknown)
(define frag_q0 (term ((,par_fn1) (,par_fn2 ,par_fn3 ,par_fn0))))
(define frag_q1 (term ((,par_fn2 ,par_fn3 ,par_fn0) (,par_fn4 ,par_fn5))))

; Capability
(define cap0 (term (,tser1 ,frag_q0)))

; Client State
(define cs0 '())                    ; Initial state, C0 = empty
(define cs1 (term (,cap0 ,excp_nil_0 ,excp_nil_1 ,excp0 ,excp1)))

; RED State
(define psa0 (term (psa ,clo2 ,as0 ,rs0 ,cs0 ,trn_fns)))
(define psa1 (term (psa ,clo3 ,as0 ,rs2 ,cs1 ,trn_fns)))

(module+ test
    ; Testing all the times
    (test-equal (redex-match? HCAP Clock clo0) #true)
    (test-equal (redex-match? HCAP Clock clo1) #true)
    (test-equal (redex-match? HCAP Clock clo2) #true)
    (test-equal (redex-match? HCAP Clock clo3) #true)
    (test-equal (redex-match? HCAP Clock clo4) #true)
    (test-equal (redex-match? HCAP Clock clo5) #true)

    (test-equal (redex-match? HCAP TimeAS tas0) #true)
    (test-equal (redex-match? HCAP TimeAS tas1) #true)
    (test-equal (redex-match? HCAP TimeAS tas2) #true)
    (test-equal (redex-match? HCAP TimeAS tas3) #true)
    
    (test-equal (redex-match? HCAP TimeRS trs0) #true)
    (test-equal (redex-match? HCAP TimeRS trs1) #true)
    (test-equal (redex-match? HCAP TimeRS trs2) #true)
    (test-equal (redex-match? HCAP TimeRS trs3) #true)
    
    (test-equal (redex-match? HCAP Time t0) #true)
    (test-equal (redex-match? HCAP Time t1) #true)
    (test-equal (redex-match? HCAP Time t2) #true)
    (test-equal (redex-match? HCAP Time t3) #true)

    (test-equal (redex-match? HCAP TimeSER tser0) #true)
    (test-equal (redex-match? HCAP TimeSER tser1) #true)
    (test-equal (redex-match? HCAP TimeSER tser2) #true)
    (test-equal (redex-match? HCAP TimeSER tser3) #true)

    ; Testing Authroization server state
    (test-equal (redex-match? HCAP AState as0) #true)
    (test-equal (redex-match? HCAP AState as1) #true)
    
    ; Testing Exceptions 
    (test-equal (redex-match? HCAP Excp excp_nil_0) #true)
    (test-equal (redex-match? HCAP Excp excp_nil_1) #true)
    (test-equal (redex-match? HCAP Excp excp0) #true)
    (test-equal (redex-match? HCAP Excp excp1) #true)

    ; Testing Resource Server state
    (test-equal (redex-match? HCAP RState rs0) #true)
    (test-equal (redex-match? HCAP RState rs1) #true)

    ; Testing fragment
    (test-equal (redex-match? HCAP Frag frag_undefined) #true)
    (test-equal (redex-match? HCAP Frag frag_unknown) #true)
    (test-equal (redex-match? HCAP Frag frag_q0) #true)
    (test-equal (redex-match? HCAP Frag frag_q1) #true)

    ; Testing Capability
    (test-equal (redex-match? HCAP Cap cap0) #true)

    ; Testing Client state
    (test-equal (redex-match? HCAP CState cs0) #true)
    (test-equal (redex-match? HCAP CState cs1) #true)

    ; Testing RED state
    (test-equal (redex-match? HCAP REDState psa0) #true)
    (test-equal (redex-match? HCAP REDState psa1) #true)
)

(define red
    (reduction-relation HCAP 

    ; T-FSH, garbage collection [DONE]
    ; new(t_as) = new(t_rs) = t_clo,
    ; new(e_rs) = nil (t of the outermost e_rs)
    ; if t_as = first(e_rs) then new(q_as) = TrnFn*(q_as, e_rs)
    (--> (psa Clock_1 AState_1 (TimeRS_1 Excp_1) CState TrnFn)
         (psa Clock_2 AState_2 (TimeRS_2 Excp_2) CState TrnFn)

         ; increment clock 
         (where Clock_2 ,(increment-clock (term Clock_1)))

         ; Update the AState
         (where AState_2 ,(flush-as (term AState_1) (term Excp_1) (term Clock_1) (term TrnFn)))

         ; Update the RState 
         (where TimeRS_2 ,(flush-rs-update-time (term TimeRS_1) (term Clock_1)))
         (where Excp_2 ,(flush-rs-update-excp (term Excp_1)))

         (computed-name (term (flush)))
    )

    ; T-UPD, client updates the internal state of auth server
    ; if Tic in C, and Tic = upd(e), and the first(e) = t_as (THE INNERMOST TIME)
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

         (computed-name (term (update-nil (ex nil (t TimeAS_1)))))

    )

    ; ; CASE 2: upd(e) = (ex Perm Time Excp)
    ; ;;; PROBLEM: Clock will increment even if the IT DOESN'T UPDATE
    ; ;;; TODO: Fix the Clock problem
    ; (--> (psa Clock_1 AState_1 RState CState TrnFn)
    ;      (psa Clock_2 AState_2 RState CState TrnFn)

    ;      ; increment clock 
    ;      (where Clock_2 ,(increment-clock (term Clock_1)))

    ;      ; find a upd(e) ticket in C
    ;      (where (Tic_1 ... (ex Perm Time Excp) Tic_3 ...) CState) 

    ;      ; update the AState
    ;      (where AState_2 ,(recv-update-astate (term AState_1) (term Excp) (term Clock_1) (term TrnFn)))

    ;      ; give this transition a name
    ;      (computed-name (term (update-excp (ex Perm Time Excp))))
    ; )
    
    ; TODO: T-RCV, client asks the resource server to recover a lost ticket

    ; ; T-DRP, the client accidentally drops some of its tickets [DONE]
    ; ; if Tic in C, then can be dropped
    ; (--> (psa Clock_1 AState RState CState_1 TrnFn)
    ;      (psa Clock_2 AState RState CState_2 TrnFn)

    ;      ; increment the clock
    ;      (where Clock_2 ,(increment-clock (term Clock_1)))

    ;      ; Find a ticket to drop 
    ;      (where (Tic_1 ... Tic_2 Tic_3 ...) CState_1)

    ;      ; Remove the ticket, and store into CState_2
    ;      (where CState_2 ,(remove (term Tic_2) (term CState_1)))

    ;      ; Give this transition a name
    ;      (computed-name (term (drop Tic_2)))
    ; )
    )
)

; <------------------- BEGIN: RED Helpers ------------------->
; Increment global clock value, this will be called from all the trnx
; Param: Clock
; Return: Clock
(define (increment-clock clock)
    (let ([val (second clock)])
         (term (clo ,(+ 1 val)))
    )
)
(trace increment-clock)

; Retrieve the innermost time in Exception
; Param: Excp 
; Return: Time
(define (get-first-excp-time excp)
    (if (eqv? (second excp) 'nil)                   ; reached the innermost excp
        (third excp)                                ; return the time
        (get-first-excp-time (fourth excp))         ; otherwise, keep going
    )
)
(trace get-first-excp-time)

; Generate a new AState, such that 
; qas' = apply excp to qas
; tas' = tclo
; Param: QState Excp Clock TrnFn
; Return: (QState TimeAS)
(define (generate-new-astate qas excp tclo TrnFn)
    (let ([newQState (get-new-qstate qas excp TrnFn)]
          [newTimeAS (term (tas ,(second tclo)))])
          (term (,newQState ,newTimeAS))
    )
)
(trace generate-new-astate)

; Sub-function, called from generate-new-astate
; Param: QState Excp TrnFn
; Return: QState
(define (get-new-qstate qas excp TrnFn)
    (if (eqv? (second excp) 'nil)           ; reached the innermost excp 
        (term ,qas)                         ; base case, return current qas
        ; apply the newly obtained state with the Perm associated to current Excp 
        (apply-excp-perm-to-state (get-new-qstate qas (fourth excp) TrnFn) (second excp) TrnFn)
    )
)
(trace get-new-qstate)

; Apply Perm to the QState based on the TrnFn list
; Param: QState Perm TrnFn
; Return: QState
(define (apply-excp-perm-to-state qstate perm TrnFn)
    (if (null? TrnFn)                   ; if the TrnFn doesn't have anything,
        (term ,qstate)                  ; stay in current state
        ; otherwise, find the (QState Perm X) element in TrnFn, and return X
        (let ([parFn (first TrnFn)])
            (let ([fn_q1 (first parFn)]         ; origin state
                  [fn_p  (second parFn)]        ; permission
                  [fn_q2 (third parFn)])        ; result state
                ; Check that (qstate perm) = (fn_q1 fn_p)
                (if (and (eqv? fn_q1 qstate)
                         (eqv? fn_p  perm))
                    (term ,fn_q2)
                    ; otherwise, check the rest of the TrnFn
                    (apply-excp-perm-to-state qstate perm (rest TrnFn)) 
                )
            )
        )
    )
)
(trace apply-excp-perm-to-state)

; ***************** PREDICATES ***************************
; Check if 2 times are the same value.
; Param Types: Clock, TimeAS, TimeRS, Time, TimeSER
; Return boolean
(define (are-times-eqv? time_1 time_2)
    (eqv? (second time_1) (second time_2))
)
(trace are-times-eqv?)

; helper tests
(module+ test
    ; Testing increment-clock
    (test-equal (increment-clock clo0) clo1)

    ; Testing get-first-excp-time
    (test-equal (get-first-excp-time excp1) t0)
    (test-equal (get-first-excp-time excp2) t1)

    ; Testing generate-new-astate
    (test-equal (generate-new-astate q0 excp1 clo3 trn_fns) as2)

    ; Testing are-times-eqv?
    (test-equal (are-times-eqv? tas0 tser2) #false)
    (test-equal (are-times-eqv? clo1 tas1) #true)

)


; /******************** T-FSH ********************/
; Update the AState with 
;;; TimeAS' = Clock
;;; If TimeAS = first(e_rs) then QStateAS = TrnFn*(q_as, e_rs)
(define (flush-as astate e_rs t_clo TrnFn)
    (let ([q_as (first  astate)]
          [t_as (second astate)]
          [c_val (second t_clo)])
        (if (are-times-eqv? t_as (get-first-excp-time e_rs))
            (generate-new-astate q_as e_rs t_clo TrnFn)            ; return (QState', TimeAS')
            (term (,q_as (tas ,c_val)))                            ; return (QState, TimeAS')
        )
    )
)
(trace flush-as)

; Update the TimeRS to the Clock 
; Param: TimeRS Clock
; Return TimeRS
(define (flush-rs-update-time t_rs t_clo)
    (let ([clo (second t_clo)])
        (term (trs ,clo))
    )
)
(trace flush-rs-update-time)

; Update the Excp to (ex nil (t last(ers)))
; Param: Excp
; Return: Excp of the form (ex nil Time)
(define (flush-rs-update-excp excp)
    (let ([new_time (second (third excp))])
        (term (ex nil (t ,new_time)))
    )
)
(trace flush-rs-update-excp)

; T-FSH tests 
(module+ test
    ; Testing flush-as
    (test-equal (flush-as as0 excp2 clo3 trn_fns) as2)      ; q_as(0) -> q_as(1), t_as(1) -> t_as(3)
    (test-equal (flush-as as1 excp1 clo3 trn_fns) as3)      ; q_as stays, time changes

    ; Testing flush-rs-update-time
    (test-equal (flush-rs-update-time trs0 clo1) trs1)      ; Changing the times
    (test-equal (flush-rs-update-time trs1 clo3) trs3)

    ; Testing flush-rs-update-excp
    (test-equal (flush-rs-update-excp excp2) (term (ex nil ,t2)))       ; make sure the exceptions' time is changed
    (test-equal (flush-rs-update-excp excp0) (term (ex nil ,t1)))
)

; /******************** END: T-FSH ********************/

(module+ test
  (test-results)
)
