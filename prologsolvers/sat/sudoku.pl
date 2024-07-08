%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% DECEMBER 15th 2010
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% SAT encoding of a Sudoku puzzle
%%% By A.D., the anonymous referee
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Problem of November 9th 2007 by "La Repubblica"
%%% (Advanced Level)

puzzle([cell(1,6,9),
        cell(2,1,4),cell(2,9,8),
        cell(3,1,7),cell(3,2,3),cell(3,4,2),cell(3,5,6),
        cell(4,1,8),cell(4,3,1),cell(4,6,3),cell(4,9,6),
        cell(5,1,6),cell(5,4,9),cell(5,5,7),cell(5,6,5),cell(5,9,3),
        cell(6,1,3),cell(6,4,1),cell(6,7,2),cell(6,9,4),
        cell(7,5,1),cell(7,6,8),cell(7,8,6),cell(7,9,7),
        cell(8,1,9),cell(8,9,5),
        cell(9,4,3) ],9).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sudoku  :-
  open('sudoku.cnf',write,Stream),
  set_output(Stream),
  puzzle(InputList,Size),
  write('ccccccccccccccccccccccccccccccccccccccccccccccccccccccccc'),nl,
  write('c  SAT encoding of an instance of SUDOKU thanks to A.D. c'),nl,
  write('ccccccccccccccccccccccccccccccccccccccccccccccccccccccccc'),nl,
  fix_vars(InputList,Size),
  boolconstraints(Size),
  rowconstraints(Size),
  columnconstraints(Size),
  squareconstraints(Size),
  close(Stream).

boolconstraints(Size) :-
  double_for(1,1,Size,k).
rowconstraints(Size) :-
  double_for(1,1,Size,i).
columnconstraints(Size) :-
  double_for(1,1,Size,j).
squareconstraints(Size) :-
  value_for(0,Size).

double_for(A,_,Size,_) :-
  A > Size, !.
double_for(A,B,Size,Par) :-
  B > Size, !,
  A1 is A + 1,
  double_for(A1,1,Size,Par).
double_for(A,B,Size,Par) :-
  digit(A,B,1,Size,List,Par),
  exactly_one(List),
  B1 is B + 1,
  double_for(A,B1,Size,Par).

digit(_A,_B,C,Size,[],_):-
     C > Size.
digit(A,B,C,Size,[Val|R],Par):-
   (Par=i, converti(C,A,B,Size,Val);
    Par=j, converti(A,C,B,Size,Val);
    Par=k, converti(A,B,C,Size,Val)),
    C1 is C + 1,
    digit(A,B,C1,Size,R,Par).

value_for(Size, Size) :- !.
value_for(Square, Size) :-
  square_clauses(Square, Size),
  Square1 is Square + 1,
  value_for(Square1, Size).

square_clauses(Square, Size) :-
  Root is integer(sqrt(Size)),
  STARTX is (Square mod Root) * Root + 1,
  STARTY is (Square // Root) * Root + 1,
  insquare(1,Size,Root,STARTX,STARTY).

insquare(K,Size,_,_,_) :- K>Size,!.
insquare(K,Size,Root,StartX,StartY) :-
  digit_square(0,0,K,Root,Size,StartX,StartY,Clause),
  exactly_one(Clause),
  K1 is K+1,
  insquare(K1,Size,Root,StartX,StartY).

digit_square(Root,_,_,Root,_,_,_,[]):-!.
digit_square(I,Root,K,Root,Size,StartX,StartY,Clause):-
  !,
  I1 is I + 1,
  digit_square(I1,0,K,Root,Size,StartX,StartY,Clause).
digit_square(I,J,K,Root,Size,StartX,StartY,[C|Clause]):-
  I1 is I+StartX,
  J1 is J+StartY,
  converti(I1,J1,K,Size,C),
  Jn is J+1,
  digit_square(I,Jn,K,Root,Size,StartX,StartY,Clause).

fix_vars([],_).
fix_vars([cell(I,J,K)|R],Size) :-
  converti(I,J,K,Size,Val),
  clause([Val]),
  fix_vars(R,Size).

converti(I,J,K,Size,Val) :-
   Val is Size*Size*(I-1)+Size*(J-1)+K.

exactly_one(L) :-
   clause(L),
   no_pair(L).

clause(L) :-
  clausola(L).

clausola([]) :-
  write('0 '),nl.
clausola([A]) :- !,
  write(A), write(' 0'),nl.
clausola([A|R]) :-
  write(A), write(' '), 
  clausola(R).

no_pair([]).
no_pair([_]).
no_pair([A|R]) :-
  A1 is -A, no_pairs(A1,R), no_pair(R).
no_pairs(_,[]).
no_pairs(A,[B|R]):-
  B1 is -B, clause([A,B1]), no_pairs(A,R).

write_vars(Size) :-
   N is Size*Size*Size - 1,
   write_vars(1,N).
write_vars(N,N) :-
   M is N + 1,
   write('X'),write(N),write(',X'),write(M).
write_vars(X,N) :-
   X < N,
   write('X'),write(X),write(','),
   X1 is X + 1,
   write_vars(X1,N).

%%%%%%%%%%% END
