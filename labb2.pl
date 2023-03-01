% Kopierad från uppgiften:
verify(InputFileName) :- see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    validProof(Prems, Goal, Proof).


lastElm([L|[]], L).
lastElm([H|T], L) :- lastElm(T, L).



isBox([H|T]) :- lastElm(H, assumption).

isList(A) :- A=[H|T].

% firstLine(Lines, FirstLine).
firstLine([H|T], H). 

% HJÄLPMETODER FÖR ATT GORA DET ENKLARE:
getLineNumber([A1|_], A1). 

% getLineProof([_, Proof, A], Proof).
getLineProof([_, Proof, A], Proof) :- \+isList(A).
getLineRule(Line, Rule) :- lastElm(Line, Rule).

% getLine(RADER, RADEN VI VILL HA, RADNUMMRET AV RADEN VI VILL HA).
getLine([H|Proof], H, LineNumber) :- getLineNumber(H, LineNumber).
getLine([A|Proof], H, LineNumber) :- getLine(Proof, H, LineNumber).

% Basfall, om det sista i bevisade är det som ska bevisas gäller beviset

% Visa att malet är ratt här
validProof(Prems, Goal, Proof) :- lastElm(Proof, LastLine),
            getLineProof(LastLine, Goal), proveLines(Prems, [], Proof, [], []).

% KANSKE PROBLEM OM EN BOX SLUTAR MED EN BOX                
box([H|Rows], Fline, Lline) :-  lastElm([H|Rows], L), 
                                getLineNumber(L, Lline), 
                                getLineNumber(H, Fline).


% MÅSTE VARA PÅ FÖLJANDE FORM:
%    proveLines(Premises, Assumptions, Proof, Prooved, ProovedBoxes);

%   INTE EN PERFEKT LÖSNING. VISSA ANTAGANDEN HAR GJORTS:
%       ASSUMPTIONS KAN ENDAST FINNAS PÅ FÖRSTA RADEN I EN BOX
%
%
%

% Om box, bevisa boxen och lägg till boxen som en bevisad box!
proveLines(Premises, Assumptions, [[H|BoxLines]|ProofLines], Prooved, ProovedBoxes) :-   isBox([H|BoxLines]),   
                                getLineProof(H, Assumption),
                                % Bevisa raderna i boxen 
                                proveLines(Premises, [Assumption|Assumptions], [H|BoxLines], Prooved, ProovedBoxes),
                                
                                % BERÄKNA första och sista radnummret i BOXEN (annars binds de inte):
                                getLineNumber(H, F), lastElm([H|BoxLines], Last), getLineNumber(Last, L), 
                                
                                % Bevisa övriga rader rekursivt:
                                proveLines(Premises, Assumptions, ProofLines, Prooved, 
                                 [box([H|BoxLines], F, L)|ProovedBoxes]). 

proveLines(Premises, Assumptions, [ToProve|ProofLines], Prooved, ProovedBoxes) :-   \+isBox(ToProve), 
                                % Bevisa nuvarande raden
                                proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve), 
                                % Bevisa resterande rader
                                proveLines(Premises, Assumptions, ProofLines, [ToProve|Prooved], ProovedBoxes).

% basfal
proveLines(_, _, [], _, _).




%%%%%%%%%%%%%%%% REGELDEFINITIONER %%%%%%%%%%%%%%%%%%%%
 %MÅSTE VARA PA FORMEN :
   % SKRIV HÄR...

%andint
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, andint(X, Y)), 
                            getLineProof(ToProve, and(Phi, Psy)), getLine(Prooved, Arg1, X),
                            getLine(Prooved, Arg1, X),
                            getLineProof(Arg1, Phi),
                            getLine(Prooved, Arg2, Y),
                            getLineProof(Arg2, Psy).

% ANDEL 1
proveLine(Premises,Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, andel1(X)), 
                            getLineProof(ToProve, LineProof), getLine(Prooved, Line, X),
                            getLineProof(Line, and(LineProof,_)).

% ANDEL 2
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, andel2(X)), 
                            getLineProof(ToProve, LineProof), getLine(Prooved, Line, X),
                            getLineProof(Line, and(_, LineProof)).

% orint1
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, orint1(X)), 
                            getLineProof(ToProve, or(LineProof, _)), 
                            getLine(Prooved, Line, X), getLineProof(Line, LineProof).

% orint2
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, orint1(X)),
                            getLineProof(ToProve, or(_, LineProof)), 
                            getLine(Prooved, Line, X), getLineProof(Line, LineProof).

% impel 
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, impel(X, Y)), 
                            getLineProof(ToProve, LineProof), 
                            getLine(Prooved, Arg1, X), getLine(Prooved, Arg2, Y), 
                            getLineProof(Arg2, imp(Phi, LineProof)), getLineProof(Arg1, Phi).

%premise
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :-   getLineRule(ToProve, premise), 
                                        getLineProof(ToProve, LineProof),  
                                        member(LineProof, Premises).

%Assumption (typ samma som för premise) 
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :-   getLineRule(ToProve, assumption), 
                                        getLineProof(ToProve, LineProof),  
                                        member(LineProof, Assumptions).

%Copy
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, copy(X)), 
                            getLineProof(ToProve, LineProof),
                            getLine(Prooved, Arg, X), getLineProof(Arg, LineProof).

% negel
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, negel(X, Y)), 
                            getLineProof(ToProve, cont), 
                            getLine(Prooved, Arg1, X), 
                            getLine(Prooved, Arg2, Y), 
                            getLineProof(Arg1, Phi), getLineProof(Arg2, neg(Phi)).

% contel DENNA ÄR LITE KNAS?
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, contel(X)), 
                            getLineProof(ToProve, _), % Denna raden är onödig såklart... 
                            getLine(Prooved, Arg, X), getLineProof(Arg, cont).

% negnegint (Inte testad?)
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, negnegint(X)), 
                            getLineProof(ToProve, neg(neg(Phi))), 
                            getLine(Prooved, Arg, X), getLineProof(Arg, Phi).

% negnegel
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, negnegel(X)), 
                            getLineProof(ToProve, Phi), getLine(Prooved, Arg, X), 
                            getLineProof(Arg, neg(neg(Phi))).

% mt
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, mt(X, Y)), 
                            getLineProof(ToProve, neg(Phi)), getLine(Prooved, Arg1, X), 
                            getLineProof(Arg1, imp(Phi, Psy)), 
                            getLine(Prooved, Arg2, Y), getLineProof(Arg2, neg(Psy)).

% lem
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, lem), 
                            getLineProof(ToProve, or(Phi, neg(Phi))).

%impint 
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, impint(X, Y)), 
                                                    getLineProof(ToProve, imp(Phi, Psy)),
                                                    member(box(Boxlines, X, Y), ProovedBoxes),
                                                    firstLine(Boxlines, First), getLineProof(First, Phi),
                                                    lastElm(Boxlines, Last), getLineProof(Last, Psy).


%negint (Fungerar)
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, negint(X, Y)), 
                                                    getLineProof(ToProve, neg(Phi)),
                                                    member(box(Boxlines, X, Y), ProovedBoxes),
                                                    firstLine(Boxlines, First), getLineProof(First, Phi),
                                                    lastElm(Boxlines, Last), getLineProof(Last, cont).


%pbc (FUNGERAR) 
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, pbc(X, Y)), 
                                                    getLineProof(ToProve, Phi),
                                                    member(box(Boxlines, X, Y), ProovedBoxes),
                                                    firstLine(Boxlines, First), getLineProof(First, neg(Phi)),
                                                    lastElm(Boxlines, Last), getLineProof(Last, cont).

%orel (Fungerar) Y-U, V-W
proveLine(Premises, Assumptions, Prooved, ProovedBoxes, ToProve) :- getLineRule(ToProve, orel(X, Y, U, V, W)),
                                                    % Raden ska bevisa Chi
                                                    getLineProof(ToProve, Chi), 
                                                    
                                                    % Rad nummer X måste visa or(Psi, Psy)
                                                    getLine(Prooved, Arg1, X), getLineProof(Arg1, or(Phi, Psy)),

                                                    % Boxen mellan y-u ska visa Chi från att ha antagit Phi
                                                    member(box(Boxlines1, Y, U), ProovedBoxes),
                                                    firstLine(Boxlines1, F1), getLineProof(F1, Phi),
                                                    lastElm(Boxlines1, L1), getLineProof(L1, Chi),
                                                    
                                                    % Boxen mellan v-w ska visa Chi från att ha antagit Psy
                                                    member(box(Boxlines2, V, W), ProovedBoxes),
                                                    firstLine(Boxlines2, F2), getLineProof(F2, Psy),
                                                    lastElm(Boxlines2, L2), getLineProof(L2, Chi).