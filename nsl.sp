(**
#Needham-Schroeder-Lowe (asymmetric)
    A, B : principal
    Kas, Kbs, K : symkey
    Na : nonce

    A -> B : {Na, A}_pubB
    B -> A : {Na, Nb, B}_pubA
    A -> B : {Nb}_pubB
**)

include Core.

channel c.

aenc enc,dec,pk.

(* identifiers *)
abstract iA : message
abstract iB : message.

(* secrety key as a func of identifier *)
abstract sk : message -> message.

(* nonces *)
abstract nA : index -> message
abstract nB : index -> message.
(* meeting: below generates an axiom that prevents attack
name n : index -> message.
*)

(* enc randomness *)
abstract r1 : index -> message
abstract r2 : index -> message
abstract r3 : index -> message.

abstract ok : message.

process A(i: index) =
  A1 : out(c, enc(<nA(i), iA>, r1(i), pk(sk(iB))));
  A2 : in(c,x);
       if fst(dec(x, sk(iA))) = nA(i)
       && snd(snd(dec(x, sk(iA)))) = iB
       then out(c, enc(fst(snd(dec(x, sk(iA)))), r3(i), pk(sk(iB)))).

process B(i: index) =
  B1 : in(c,x);
       out(c, enc(<fst(dec(x,sk(iB))), <nB(i), iB>>, r2(i), pk(sk(iA))));
  B2 : in(c,x);
       if dec(x, sk(iB)) = nB(i)
       then out(c, ok).

(*system (!_i A(i) | !_i B(i)). *)

abstract i0 : index
abstract i1 : index.

system (A(i0) | B(i0) | B(i1)).

lemma leak :
  exists (t:timestamp), exists (i:index),
    happens(t) && att(frame@t) = nB(i).
