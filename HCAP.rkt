#lang scheme
(require redex)
(require racket/trace)

(define-language HCAP
;;; SA (Permissions, Automaton states, initial state, partial transition)
    ;;; [Perms  (Perm State)]   ; (Operation, Resource)
    [RS     (rs natural)]     ; resource servers
    [Perm   (RS ...)]      ; The exercising operation, can be whatever you want (?)
    [QState (q natural)]    ; q state
    [Q    (QState ...)]     ; set of automaton states
    ;;; [TrnFn  (State Perm State)]   ; Partial transition f'n: (State, permission, State), where State = State in StatPerm, but State != State in TranPerm
    
    ;;; Protocol states 
    [Tik    Upd                 ; 2 types of ticket; upd(e) or cap(tser, F)
            Cap]

    [Cap    (TimeSER Frag)]        ; cap(tser , F)
    [Frag   (TrnFn ...)]        ; Frag identifies the permissions allowed in state Q, and the transitions out of state Q
    [Upd    (Excp)]             ; upd(e)

    ;;; also used for ers
    [Excp   (Perm Time Excp)    ; e::= ex(p, t, e)
            (nil Time)]         ;   := nil(t)

    ;;; Security Automaton State
    ;;; Serial[id] is used as the serial number of the next cap issued by the SA for session ID.
    ;;; sa (monitor[id]) (state[id]) (serial[id])
    [Clock   (tclo natural)]             ; used for global Clock, 
    [TimeRS  (trs  natural)]            ; resource time
    [Time    (t    natural)]            ; exception time
    [TimeAS  (tas  natural)]            ; authorization server time
    [TimeSER (tser natural)]            ; capability time

    [AState (State TimeAS)]               ; pair (qas, tas). State is the last known by the SA, Time is the acknowledgement by the SA
    [RState (TimeRS Excp)]                ; pair (trs, ers). 
    [CState (Tik ...)]

    ;;; this is q \in Q
    ;;; [State (st )]

    ; protocol state = (t_clo, A, R, C)
    [PState (pst Clock AState RState CState)]
)

(define q0 (term (q 0)))    ; initial state

;;; initial state for Protocol state
(define t0 (term (time 0)))
(define t1 (term (time 1)))
(define t2 (term (time 2)))

(define excp_nil_t0 (term (nil ,t0)))

(define a0 (term (,q0 ,t1)))
(define r0 (term (,t1 ,excp_nil_t0)))

;γ0 = (2, A0 , R0 , Empty) where A0 = (q0 , 1), R0 = (1, nil(0))
(define p0 (term (pst ,t0 ,a0 ,r0 )))


(module+ test
  (test-equal (redex-match? HCAP Time t0) #true)
  (test-equal (redex-match? HCAP Time t1) #true)
  (test-equal (redex-match? HCAP Time t2) #true)
  
  (test-equal (redex-match? HCAP Excp excp_nil_t0) #true)
  
  (test-equal (redex-match? HCAP RState r0) #true)
)

(module+ test
  (test-results)
)

;;; input a PState, out comes a PState
;;; (define red
;;;     (reduction-relation HCAP
        ; T-ISS, Authorization server issues a capability to the client
;;;     (--> (pst Clock AState RState CState_1)
;;;          (pst Clock AState RState CState_2)
;;;     )  ; end of T-ISS
;;;     )   ; end of reduction-relation
;;; )   ; end of define red