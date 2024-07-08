# https://leancop.de/nanocop-i/

code = """
%% File: nanocopi20_swi.pl  -  Version: 2.0  -  Date: 1 May 2021
%%
%% Purpose: nanoCoP-i: A Non-clausal Connection Prover for
%%                     Intuitionistic First-Order Logic
%%
%% Author:  Jens Otten
%% Web:     www.leancop.de/nanocop-i/
%%
%% Usage:   prove(F,P).  % where F is a first-order formula, e.g.
%%                       %  F=((p,all X:(p=>q(X)))=>all Y:q(Y))
%%                       %  and P is the returned connection proof
%%
%% Copyright: (c) 2017-2021 by Jens Otten
%% License:   GNU General Public License

:- set_prolog_flag(occurs_check,true).  % global occurs check on

:- dynamic(pathlim/0), dynamic(lit/4).

% definitions of logical connectives and quantifiers

:- op(1130,xfy,<=>). :- op(1110,xfy,=>). :- op(500, fy,'~').
:- op( 500, fy,all). :- op( 500, fy,ex). :- op(500,xfy,:).

% -----------------------------------------------------------------
% prove(F,Proof) - prove formula F

prove(F,Proof) :- prove2(F,[cut,comp(6)],Proof).

prove2(F,Set,Proof) :-
    bmatrix(F,Set,Mat), retractall(lit(_,_,_,_)),
    assert_matrix(Mat), prove(Mat,1,Set,Proof).

% start rule
prove(Mat,PathLim,Set,[(I^0)^V:Proof]) :-
    ( member(scut,Set) -> ( append([(I^0)^V^VS:Cla1|_],[!|_],Mat) ;
        member((I^0)^V^VS:Cla,Mat), positiveC(Cla,Cla1) ) -> true ;
        ( append(MatC,[!|_],Mat) -> member((I^0)^V^VS:Cla1,MatC) ;
        member((I^0)^V^VS:Cla,Mat), positiveC(Cla,Cla1) ) ),
    prove(Cla1,Mat,[],[I^0],PathLim,[],PreS,VarS,Set,Proof),
    append(VarS,VS,VarS1), domain_cond(VarS1), prefix_unify(PreS).

prove(Mat,PathLim,Set,Proof) :-
    retract(pathlim) ->
    ( member(comp(PathLim),Set) -> prove(Mat,1,[],Proof) ;
      PathLim1 is PathLim+1, prove(Mat,PathLim1,Set,Proof) ) ;
    member(comp(_),Set) -> prove(Mat,1,[],Proof).

% axiom
prove([],_,_,_,_,_,[],[],_,[]).

% decomposition rule
prove([J^K:Mat1|Cla],MI,Path,PI,PathLim,Lem,PreS,VarS,Set,Proof) :-
    !, member(I^V^FV:Cla1,Mat1),
    prove(Cla1,MI,Path,[I,J^K|PI],PathLim,Lem,PreS1,VarS1,Set,Proof1),
    prove(Cla,MI,Path,PI,PathLim,Lem,PreS2,VarS2,Set,Proof2),
    append(PreS2,PreS1,PreS), append(FV,VarS1,VarS3),
    append(VarS2,VarS3,VarS), Proof=[J^K:I^V:Proof1|Proof2].

% reduction and extension rules
prove([Lit:Pre|Cla],MI,Path,PI,PathLim,Lem,PreS,VarS,Set,Proof) :-
    Proof=[Lit:Pre,I^V:[NegLit:PreN|Proof1]|Proof2],
    \+ (member(LitC,[Lit:Pre|Cla]), member(LitP,Path), LitC==LitP),
    (-NegLit=Lit;-Lit=NegLit) ->
       ( member(LitL,Lem), Lit:Pre==LitL, ClaB1=[], Proof1=[],
         I=l, V=[], PreN=Pre, PreS3=[], VarS3=[]
         ;
         member(NegL:PreN,Path), unify_with_occurs_check(NegL,NegLit),
         ClaB1=[], Proof1=[], I=r, V=[],
         \+ \+ prefix_unify([Pre=PreN]), PreS3=[Pre=PreN], VarS3=[]
         ;
         lit(NegLit:PreN,ClaB,Cla1,Grnd1),
         ( Grnd1=g -> true ; length(Path,K), K<PathLim -> true ;
           \+ pathlim -> assert(pathlim), fail ),
         \+ \+ prefix_unify([Pre=PreN]),
         prove_ec(ClaB,Cla1,MI,PI,I^V^FV:ClaB1,MI1),
         prove(ClaB1,MI1,[Lit:Pre|Path],[I|PI],PathLim,Lem,PreS1,VarS1,
               Set,Proof1), PreS3=[Pre=PreN|PreS1], append(VarS1,FV,VarS3)
       ),
       ( member(cut,Set) -> ! ; true ),
       prove(Cla,MI,Path,PI,PathLim,[Lit:Pre|Lem],PreS2,VarS2,Set,Proof2),
       append(PreS3,PreS2,PreS), append(VarS2,VarS3,VarS).

% extension clause (e-clause)
prove_ec((I^K)^V:ClaB,IV:Cla,MI,PI,ClaB1,MI1) :-
    append(MIA,[(I^K1)^V1:Cla1|MIB],MI), length(PI,K),
    ( ClaB=[J^K:[ClaB2]|_], member(J^K1,PI),
      unify_with_occurs_check(V,V1), Cla=[_:[Cla2|_]|_],
      append(ClaD,[J^K1:MI2|ClaE],Cla1),
      prove_ec(ClaB2,Cla2,MI2,PI,ClaB1,MI3),
      append(ClaD,[J^K1:MI3|ClaE],Cla3),
      append(MIA,[(I^K1)^V1:Cla3|MIB],MI1)
      ;
      (\+member(I^K1,PI);V\==V1) ->
      ClaB1=(I^K)^V:ClaB, append(MIA,[IV:Cla|MIB],MI1) ).

% -----------------------------------------------------------------
% assert_matrix(Matrix) - write matrix into Prolog's database

assert_matrix(M) :-
    member(IV:C,M), assert_clauses(C,IV:ClaB,ClaB,IV:ClaC,ClaC).
assert_matrix(_).

assert_clauses(C,ClaB,ClaB1,ClaC,ClaC1) :- !,
    append(ClaD,[M|ClaE],C),
    ( M=J^K:Mat -> append(MatA,[IV:Cla|MatB],Mat),
                   append([J^K:[IV:ClaB2]|ClaD],ClaE,ClaB1),
                   append([IV:ClaC2|MatA],MatB,Mat1),
                   append([J^K:Mat1|ClaD],ClaE,ClaC1),
                   assert_clauses(Cla,ClaB,ClaB2,ClaC,ClaC2)
                 ; append(ClaD,ClaE,ClaB1), ClaC1=C,
                   (ground(C) -> Grnd=g ; Grnd=n),
                   assert(lit(M,ClaB,ClaC,Grnd)), fail ).

% -----------------------------------------------------------------
% bmatrix(Formula,Set,Matrix) - generate indexed matrix

bmatrix(F,Set,M) :-
    univar(F,[],F1),
    ( member(conj,Set), F1=(A=>C) ->
        bmatrix(A:[],1,MA,[],[],[],_,1,J,_),
        bmatrix(C:[],0,MC,[],[],[],_,J,_,_), ( member(reo(I),Set) ->
        reorderC([MA],[_:MA1],I), reorderC([MC],[_:MC1],I) ;
        _:MA1=MA, _:MC1=MC ), append(MC1,[!|MA1],M)
      ; bmatrix(F1:[],0,M1,[],[],[],_,1,_,_), ( member(reo(I),Set) ->
        reorderC([M1],[_:M],I) ; _:M=M1 ) ).

bmatrix((F1<=>F2):Pre,Pol,M,FreeV,FV,VSet,Paths,I,I1,K) :- !,
    bmatrix(((F1=>F2),(F2=>F1)):Pre,Pol,M,FreeV,FV,VSet,Paths,I,I1,K).

bmatrix((~F):Pre,Pol,M,FreeV,FV,VSet,Paths,I,I1,K) :- !,
    ( Pol=0 -> Pr=[I^FreeV1], FV1=FV ; Pr=[V], FV1=[V|FV] ),
    Pol1 is (1-Pol), append(Pre,Pr,Pre1), append(FreeV,FV,FreeV1),
    I2 is I+1, bmatrix(F:Pre1,Pol1,M,FreeV,FV1,VSet,Paths,I2,I1,K).

bmatrix(F:Pre,Pol,M,FreeV,FV,VSet,Paths,I,I1,K) :-
    F=..[C,X:F1], bma(uni,C,Pol), !,
    ( C=all -> append(Pre,[V],Pre1), FV1=[V|FV] ; Pre1=Pre, FV1=FV ),
    bmatrix(F1:Pre1,Pol,M,FreeV,[X|FV1],[X:Pre1|VSet],Paths,I,I1,K).

bmatrix(F:Pre,Pol,M,FreeV,FV,VSet,Paths,I,I1,K) :-
    F=..[C,X:F1], bma(exist,C,Pol), !,
    ( C=all -> append(Pre,[I^FreeV1],Pre1) ; Pre1=Pre ),
    append(FreeV,FV,FreeV1), I2 is I+1,
    copy_term((X,F1,FreeV1),((I^FreeV1^Pre1),F2,FreeV1)),
    bmatrix(F2:Pre1,Pol,M,FreeV,FV,VSet,Paths,I2,I1,K).

bmatrix(F:Pre,Pol,J^K:M3,FreeV,FV,VSet,Paths,I,I1,K) :-
    F=..[C,F1,F2], bma(alpha,C,Pol,Pol1,Pol2), !,
    ( C=(=>) -> append(Pre,[I^FreeV1],Pre1) ; Pre1=Pre ),
    append(FreeV,FV,FreeV1), I2 is I+1,
    bmatrix(F1:Pre1,Pol1,J^K:M1,FreeV,FV,VSet,Paths1,I2,I3,K),
    bmatrix(F2:Pre1,Pol2,_:M2,FreeV,FV,VSet,Paths2,I3,I1,K),
    Paths is Paths1*Paths2,
    (Paths1>Paths2 -> append(M2,M1,M3) ; append(M1,M2,M3)).

bmatrix(F:Pre,Pol,I^K:[(I2^K)^FV1^VSet1:C3],FreeV,FV,VSet,Paths,I,I1,K) :-
    F=..[C,F1,F2], bma(beta,C,Pol,Pol1,Pol2), !,
    ( C=(=>) -> append(Pre,[V],Pre2), FV2=[V|FV] ; Pre2=Pre, FV2=FV ),
    ( FV=[] -> FV1=FV2, VSet1=VSet, F3=F1, F4=F2, Pre1=Pre2 ;
      copy_term((FV2,VSet,F1,F2,Pre2,FreeV),(FV1,VSet1,F3,F4,Pre1,FreeV)) ),
    append(FreeV,FV1,FreeV1),  I2 is I+1, I3 is I+2,
    bmatrix(F3:Pre1,Pol1,M1,FreeV1,[],[],Paths1,I3,I4,K),
    bmatrix(F4:Pre1,Pol2,M2,FreeV1,[],[],Paths2,I4,I1,K),
    Paths is Paths1+Paths2,
    ( (M1=_:[_^[]^_:C1];[M1]=C1), (M2=_:[_^[]^_:C2];[M2]=C2) ->
      (Paths1>Paths2 -> append(C2,C1,C3) ; append(C1,C2,C3)) ).

bmatrix(A:Pre,0,I^K:[(I2^K)^FV1^VSet1:[A1:Pre1]],FreeV,FV,VSet,1,I,I1,K) :-
    !, copy_term((FV,VSet,A,Pre,FreeV),(FV1,VSet1,A1,Pre1,FreeV)),
    I2 is I+1, I1 is I+2.

bmatrix(A:Pre,1,I^K:[(I2^K)^FV1^VSet1:[-A1:(-Pre1)]],FreeV,FV,VSet,1,I,I1,K) :-
    copy_term((FV,VSet,A,Pre,FreeV),(FV1,VSet1,A1,Pre1,FreeV)),
    I2 is I+1, I1 is I+2.

bma(alpha,',',1,1,1). bma(alpha,(;),0,0,0). bma(alpha,(=>),0,1,0).
bma(beta,',',0,0,0).  bma(beta,(;),1,1,1).  bma(beta,(=>),1,0,1).
bma(exist,all,0). bma(exist,ex,1). bma(uni,all,1). bma(uni,ex,0).

% -----------------------------------------------------------------
% positiveC(Clause,ClausePos) - generate positive start clause

positiveC([],[]).
positiveC([M|C],[M3|C2]) :-
    ( M=I^K:M1 -> positiveM(M1,M2),M2\=[],M3=I^K:M2 ; -_:_\=M,M3=M ),
    positiveC(C,C2).

positiveM([],[]).
positiveM([I:C|M],M1) :-
    ( positiveC(C,C1) -> M1=[I:C1|M2] ; M1=M2 ), positiveM(M,M2).

% -----------------------------------------------------------------
%  reorderC([Matrix],[MatrixReo],I) - reorder clauses

reorderC([],[],_).
reorderC([M|C],[M1|C1],I) :-
    ( M=J^K:M2 -> reorderM(M2,M3,I), length(M2,L), I1 is I mod (L*L),
      mreord(M3,M4,I1), M1=J^K:M4 ; M1=M ), reorderC(C,C1,I).

reorderM([],[],_).
reorderM([J:C|M],[J:D|M1],I) :- reorderC(C,D,I), reorderM(M,M1,I).

mreord(M,M,0) :- !.
mreord(M,M1,I) :-
    mreord1(M,I,X,Y), append(Y,X,M2), I1 is I-1, mreord(M2,M1,I1).

mreord1([],_,[],[]).
mreord1([C|M],A,M1,M2) :-
    B is 67*A, I is B rem 101, I1 is I mod 2,
    ( I1=1 -> M1=[C|X], M2=Y ; M1=X, M2=[C|Y] ), mreord1(M,I,X,Y).

% -----------------------------------------------------------------
% prefix_unify(PrefixEquations) - prefix unification

prefix_unify([]).
prefix_unify([S=T|G]) :- (-S2=S -> T2=T ; -S2=T, T2=S),
                         flatten([S2,_],S1), flatten(T2,T1),
                         tunify(S1,[],T1), prefix_unify(G).

tunify([],[],[]).
tunify([],[],[X|T])       :- tunify([X|T],[],[]).
tunify([X1|S],[],[X2|T])  :- (var(X1) -> (var(X2), X1==X2);
                             (\+var(X2), unify_with_occurs_check(X1,X2))),
                             !, tunify(S,[],T).
tunify([C|S],[],[V|T])    :- \+var(C), !, var(V), tunify([V|T],[],[C|S]).
tunify([V|S],Z,[])        :- unify_with_occurs_check(V,Z), tunify(S,[],[]).
tunify([V|S],[],[C1|T])   :- \+var(C1), V=[], tunify(S,[],[C1|T]).
tunify([V|S],Z,[C1,C2|T]) :- \+var(C1), \+var(C2), append(Z,[C1],V1),
                             unify_with_occurs_check(V,V1),
                             tunify(S,[],[C2|T]).
tunify([V,X|S],[],[V1|T]) :- var(V1), tunify([V1|T],[V],[X|S]).
tunify([V,X|S],[Z1|Z],[V1|T]) :- var(V1), append([Z1|Z],[Vnew],V2),
                                 unify_with_occurs_check(V,V2),
                                 tunify([V1|T],[Vnew],[X|S]).
tunify([V|S],Z,[X|T])     :- (S=[]; T\=[]; \+var(X)) ->
                             append(Z,[X],Z1), tunify([V|S],Z1,T).

% -----------------------------------------------------------------
% domain_cond(VariableSet) - check domain condition

domain_cond([]).
domain_cond([X:Pre|VarS]) :- addco(X,Pre), domain_cond(VarS).

addco(X,_)          :- (atomic(X);var(X);X==[[]]), !.
addco(_^_^Pre1,Pre) :- !, prefix_unify([-Pre1=Pre]).
addco(T,Pre)        :- T=..[_,T1|T2], addco(T1,Pre), addco(T2,Pre).

% ----------------------------
% create unique variable names

univar(X,_,X)  :- (atomic(X);var(X);X==[[]]), !.
univar(F,Q,F1) :-
    F=..[A,B|T], ( (A=ex;A=all),B=X:C -> delete2(Q,X,Q1),
    copy_term((X,C,Q1),(Y,D,Q1)), univar(D,[Y|Q],E), F1=..[A,Y:E] ;
    univar(B,Q,B1), univar(T,Q,T1), F1=..[A,B1|T1] ).

% delete variable from list
delete2([],_,[]).
delete2([X|T],Y,T1) :- X==Y, !, delete2(T,Y,T1).
delete2([X|T],Y,[X|T1]) :- delete2(T,Y,T1).

"""


# adding tptp support
code += """

%% File: nanocop_tptp2.pl  -  Version: 1.0  -  Date: 17 January 2017
%%
%% Purpose: 1. Translate formula from TPTP into leanCoP syntax
%%          2. Add equality axioms to the given formula
%%
%% Author:  Jens Otten
%% Web:     www.leancop.de/nanocop/
%%
%% Usage: leancop_tptp2(X,F). % where X is a problem file using TPTP
%%                            %  syntax and F the translated formula
%%        leancop_equal(F,G). % where F is a formula and G the
%%                            %  formula with added equality axioms
%%
%% Copyright: (c) 2009-2017 by Jens Otten
%% License:   GNU General Public License


% definitions of logical connectives and quantifiers

% leanCoP syntax
:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
%                      % disjunction (;)
%                      % conjunction (,)
:- op( 500, fy, ~).    % negation
:- op( 500, fy, all).  % universal quantifier
:- op( 500, fy, ex).   % existential quantifier
:- op( 500,xfy, :).

% TPTP syntax
:- op(1130, xfy, <~>).  % negated equivalence
:- op(1110, xfy, <=).   % implication
:- op(1100, xfy, '|').  % disjunction
:- op(1100, xfy, '~|'). % negated disjunction
:- op(1000, xfy, &).    % conjunction
:- op(1000, xfy, ~&).   % negated conjunction
:- op( 500, fy, !).     % universal quantifier
:- op( 500, fy, ?).     % existential quantifier
:- op( 400, xfx, =).    % equality
:- op( 300, xf, !).     % negated equality (for !=)
:- op( 299, fx, $).     % for $true/$false

% TPTP syntax to leanCoP syntax mapping

op_tptp2((A<=>B),(A1<=>B1),   [A,B],[A1,B1]).
op_tptp2((A<~>B),~((A1<=>B1)),[A,B],[A1,B1]).
op_tptp2((A=>B),(A1=>B1),     [A,B],[A1,B1]).
op_tptp2((A<=B),(B1=>A1),     [A,B],[A1,B1]).
op_tptp2((A|B),(A1;B1),       [A,B],[A1,B1]).
op_tptp2((A'~|'B),~((A1;B1)), [A,B],[A1,B1]).
op_tptp2((A&B),(A1,B1),       [A,B],[A1,B1]).
op_tptp2((A~&B),~((A1,B1)),   [A,B],[A1,B1]).
op_tptp2(~A,~A1,[A],[A1]).
op_tptp2((! [V]:A),(all V:A1),     [A],[A1]).
op_tptp2((! [V|Vars]:A),(all V:A1),[! Vars:A],[A1]).
op_tptp2((? [V]:A),(ex V:A1),      [A],[A1]).
op_tptp2((? [V|Vars]:A),(ex V:A1), [? Vars:A],[A1]).
op_tptp2($true,(true___=>true___),      [],[]).
op_tptp2($false,(false___ , ~ false___),[],[]).
op_tptp2(A=B,~(A1=B),[],[]) :- \+var(A), A=(A1!).
op_tptp2(P,P,[],[]).


%%% translate into leanCoP syntax

leancop_tptp2(File,F) :- leancop_tptp2(File,'',[_],F,_).

leancop_tptp2(File,AxPath,AxNames,F,Con) :-
    open(File,read,Stream), ( fof2cop(Stream,AxPath,AxNames,A,Con)
    -> close(Stream) ; close(Stream), fail ),
    ( Con=[] -> F=A ; A=[] -> F=Con ; F=(A=>Con) ).

fof2cop(Stream,AxPath,AxNames,F,Con) :-
    read(Stream,Term),
    ( Term=end_of_file -> F=[], Con=[] ;
      ( Term=..[fof,Name,Type,Fml|_] ->
        ( \+member(Name,AxNames) -> true ; fml2cop([Fml],[Fml1]) ),
        ( Type=conjecture -> Con=Fml1 ; Con=Con1 ) ;
        ( Term=include(File), AxNames2=[_] ;
          Term=include(File,AxNames2) ) -> name(AxPath,AL),
          name(File,FL), append(AL,FL,AxL), name(AxFile,AxL),
          leancop_tptp2(AxFile,'',AxNames2,Fml1,_), Con=Con1
      ), fof2cop(Stream,AxPath,AxNames,F1,Con1),
      ( Term=..[fof,N,Type|_], (Type=conjecture;\+member(N,AxNames))
      -> (F1=[] -> F=[] ; F=F1) ; (F1=[] -> F=Fml1 ; F=(Fml1,F1)) )
    ).

fml2cop([],[]).
fml2cop([F|Fml],[F1|Fml1]) :-
    op_tptp2(F,F1,FL,FL1) -> fml2cop(FL,FL1), fml2cop(Fml,Fml1).


%%% add equality axioms

leancop_equal(F,F1) :-
    collect_predfunc([F],PL,FL), append(PL2,[(=,2)|PL3],PL),
    append(PL2,PL3,PL1) -> basic_equal_axioms(F0),
    subst_pred_axioms(PL1,F2), (F2=[] -> F3=F0 ; F3=(F0,F2)),
    subst_func_axioms(FL,F4), (F4=[] -> F5=F3 ; F5=(F3,F4)),
    ( F=(A=>C) -> F1=((F5,A)=>C) ; F1=(F5=>F) ) ; F1=F.

basic_equal_axioms(F) :-
    F=(( all X:(X=X) ),
       ( all X:all Y:((X=Y)=>(Y=X)) ),
       ( all X:all Y:all Z:(((X=Y),(Y=Z))=>(X=Z)) )).

% generate substitution axioms

subst_pred_axioms([],[]).
subst_pred_axioms([(P,I)|PL],F) :-
    subst_axiom(A,B,C,D,E,I), subst_pred_axioms(PL,F1), P1=..[P|C],
    P2=..[P|D], E=(B,P1=>P2), ( F1=[] -> F=A ; F=(A,F1) ).

subst_func_axioms([],[]).
subst_func_axioms([(P,I)|FL],F) :-
    subst_axiom(A,B,C,D,E,I), subst_func_axioms(FL,F1), P1=..[P|C],
    P2=..[P|D], E=(B=>(P1=P2)), ( F1=[] -> F=A ; F=(A,F1) ).

subst_axiom((all X:all Y:E),(X=Y),[X],[Y],E,1).
subst_axiom(A,B,[X|C],[Y|D],E,I) :-
    I>1, I1 is I-1, subst_axiom(A1,B1,C,D,E,I1),
    A=(all X:all Y:A1), B=((X=Y),B1).

% collect predicate & function symbols

collect_predfunc([],[],[]).
collect_predfunc([F|Fml],PL,FL) :-
    ( ( F=..[<=>|F1] ; F=..[=>|F1] ; F=..[;|F1] ; F=..[','|F1] ;
        F=..[~|F1] ; (F=..[all,_:F2] ; F=..[ex,_:F2]), F1=[F2] ) ->
      collect_predfunc(F1,PL1,FL1) ; F=..[P|Arg], length(Arg,I),
      I>0 ->  PL1=[(P,I)], collect_func(Arg,FL1) ; PL1=[], FL1=[] ),
    collect_predfunc(Fml,PL2,FL2),
    union1(PL1,PL2,PL), union1(FL1,FL2,FL).

collect_func([],[]).
collect_func([F|FunL],FL) :-
    ( \+var(F), F=..[F1|Arg], length(Arg,I), I>0 ->
      collect_func(Arg,FL1), union1([(F1,I)],FL1,FL2) ; FL2=[] ),
    collect_func(FunL,FL3), union1(FL2,FL3,FL).

union1([],L,L).
union1([H|L1],L2,L3) :- member(H,L2), !, union1(L1,L2,L3).
union1([H|L1],L2,[H|L3]) :- union1(L1,L2,L3).

"""
