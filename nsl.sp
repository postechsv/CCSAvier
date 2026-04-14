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

system (!_i A(i) | !_i B(i)).

(* constructions for fixing the indended trace for computational attack *)
abstract i0 : index
abstract i1 : index.

abstract nQ : message  (* nonce of the attacker *)
abstract iQ : message. (* identifier of the attacker *)

axiom step0 : pred(A1(i0)) = init
axiom step1 : pred(B1(i0)) = A1(i0)
axiom step2 : pred(A2(i0)) = B1(i0)
axiom step3 : pred(B1(i1)) = A2(i0).

axiom a1_to_b1 : input@B1(i0) = output@A1(i0)
axiom b1_to_a2 : input@A2(i0) = output@B1(i0)
axiom a2_to_b1 : input@B1(i1) = output@A2(i0).

axiom trace : happens(B1(i1)).

axiom ambiguity : nB(i0) = <nQ, iQ>. (* attack by Bana et al. *)

lemma _ : happens(A2(i0)).
Proof.
  use trace. use step3.
  auto.
Qed.

(* main theorem *)
lemma leak :
  exists (t:timestamp), exists (i:index),
    happens(t) && att(frame@t) = nB(i).
Proof.
  exists B1(i1).
  exists i0. 
  split.
  - use trace; auto.
  - use trace.
    use step0. use step1. use step2. use step3.
    use a1_to_b1. use b1_to_a2. use a2_to_b1.


  admit.
Qed.
