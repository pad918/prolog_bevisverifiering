% For SICStus, uncomment line below: (needed for member/2)
%:- use_module(library(lists)).
% Load model, initial state and formula from file.
verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [], F).

% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.
%

% Should evaluate to true iff the sequent below is valid.
%
% (T,L), S |- F
% U
% To execute: consult('your_file.pl'). verify('input.txt').
%--------------------------------------------------

% valid_in_all: P är listan av element som ska undersökas för formeln F DÖP OM?
valid_in_all(T, L, [], U, F).
valid_in_all(T, L, [H|P], U, F) :- 
    check(T, L, H, U, F), valid_in_all(T, L, P, U, F).

%--------------------------------------------------

% Literals: Checking the validity of atoms in S
check(_, L, S, [], P) :- member([S, V], L), member(P, V).

% Neg
%check(_, L, S, [], neg(P)) :- \+ check(_, L, S, [], P). <--- SMARTARE
check(_, L, S, [], neg(P)) :- member([S, V], L), \+ member(P, V).

%--------------------------------------------------

% And
check(T, L, S, [], and(Phi, Psi)) :- 
        check(T, L, S, [], Phi), check(T, L, S, [], Psi).

% Or
check(T, L, S, [], or(Phi, Psi)) :- 
        check(T, L, S, [], Phi). % V1

check(T, L, S, [], or(Phi, Psi)) :- 
        check(T, L, S, [], Psi). % V2

%------------------

% AX
check(T, L, S, [], ax(Phi)) :- member([S, P], T), 
        valid_in_all(T, L, P, [], Phi).

% EX
check(T, L, S, [], ex(Phi)) :- member([S, P], T), 
        member(NS, P), check(T, L, NS, [], Phi).

%-------------------

% AG
check(T, L, S, U, ag(Phi)) :-
        % S tillhör U
        member(S, U).

check(T, L, S, U, ag(Phi)) :- 
        % S tillhör inte U
        \+member(S, U),
        check(T, L, S, [], Phi), 
        member([S, P], T),
        valid_in_all(T, L, P, [S|U], ag(Phi)).

% EG
%BASFALL för regeln och löv?
check(T, L, S, U, eg(Phi)) :-
        % S tillhör U
        member(S, U).

check(T, L, S, U, eg(Phi)) :- 
        % S tillhör inte U
        \+member(S, U),
        check(T, L, S, [], Phi), 
        member([S, P], T), 
        (
            (
                member(NS, P), check(T, L, NS, [S|U], eg(Phi))
            )
        ).
               
%--------------------
% EF
check(T, L, S, U, ef(Phi)) :-  
        \+member(S, U), 
        check(T, L, S, [], Phi).

check(T, L, S, U, ef(Phi)) :- 
        \+member(S, U),
        member([S, P], T), 
            (
                %P=[] ; 
                (
                    member(NS, P), check(T, L, NS, [S|U], ef(Phi))
                )
            ).

% AF
check(T, L, S, U, af(Phi)) :-  
        \+member(S, U), 
        check(T, L, S, [], Phi).

check(T, L, S, U, af(Phi)) :- 
        \+member(S, U),
        member([S, P], T),
        valid_in_all(T, L, P, [S|U], af(Phi)).

