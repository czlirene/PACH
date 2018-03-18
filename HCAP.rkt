#lang scheme
(require redex)
(require racket/trace)

(define-language HCAP
    ;;; SA (Permissions, Automaton states, initial state, partial transition)
    [Perm   ]
    [PTrans (AState Perm)]
    []
    ;;; Protocol states 
    [Clock  (clock  natural)]
    [Time   (time   natural))]
    ;;; ers is the transitioning permissions, should prob be list?
    [Except (ers    )]
    [AuthSS (QState Time)]
    [RsrcSS (Serial )]
    [Client (Tik ...)]
    [Tik    Update
            CapC]
    ;;; Set of tickets
    [Update (p t e')]
    [CapC   (tser, F)]

    [TranID Issue
            Request
            Flush
            Update
            Recover
            Drop]
    [Tiks   (Tik ...)]

    [State  (st )]
)