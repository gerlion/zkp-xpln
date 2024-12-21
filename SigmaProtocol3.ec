(* A formalisation of Stern-style Sigma protocols *)
require import AllCore DBool.
require import Int IntDiv.
require import Distr.
require import List.

theory SigmaProtocol.
  type statement.
  type witness. (* witness to the statement *)
  type message.
  type secret. (* this may relate to the message *)
  type response.

  type transcript = message * int * response.
(*   op dm: message   distr. *)
  op de: int distr.
(*   op dz: response  distr. *)

  op R (x: statement) (w: witness): bool.

  module type SigmaScheme = {
    proc gen() : statement * witness
    proc commit(x: statement, w: witness) : message * secret
    proc test(x: statement, m: message) : int
    proc respond(sw: statement * witness, ms: message * secret, e: int) : response
    proc verify(x: statement, m: message, e: int, z: response) : bool
  }.

  module type SigmaAlgorithms = {
    proc soundness(x: statement, m: message, z: response, z': response,
      z'': response) : witness option
    proc simulate(x: statement, e: int) : message * response
  }.

  module Completeness (S: SigmaScheme) = {
    proc main(x: statement, w: witness) : bool = {
      var e, m, s, z, b;

      (m, s) <@ S.commit(x, w);
      e      <@ S.test(x, m);
      z      <@ S.respond((x, w), (m, s), e);
      b      <@ S.verify(x, m, e, z);

      return b;
    }
  }.

  
  (* Simplier of correctness which if proven for all values of e is equiv to the other defintion  *)
  module CompletenessSimp (S: SigmaScheme) = {
    proc main(x: statement, w: witness, e :int) : bool = {
      var m, s, z, b;

      (m, s) <@ S.commit(x, w);
      z      <@ S.respond((x, w), (m, s), e);
      b      <@ S.verify(x, m, e, z);

      return b;
    }
  }.
  
  module Run (S: SigmaScheme) = {
    proc main() : statement * message * int * response = {
      var x, w, m, s, e, z;

      (x, w) <@ S.gen();
      (m, s) <@ S.commit(x, w);
      e      <@ S.test(x, m);
      z      <@ S.respond((x, w), (m, s), e);

      return (x, m, e, z);
    }
  }.
  
  (*
    Special soundness is supposed to be a PPTA.
    S(m, e, z, e', z') → (x, w) in R
    This is restricated to the case where the challenge space is (Z_3)
    and we extract when we have accepting converstations for all
    possible challenges
  *)
  module type SigmaFaker = {
    proc fake() : statement*message*response*response*response
  }.
  
  module SpecialSoundnessExperiment (S: SigmaScheme, A: SigmaAlgorithms, F : SigmaFaker) = {
    proc main( )
    : bool = {
      var sto, w, r, v, v', v'', x,m,z,z',z'';
      (x,m,z,z',z'') <@  F.fake();

      sto <@ A.soundness(x, m, z, z', z'');
      w  <- oget sto;
      r  <- R x w;
      v  <@ S.verify(x, m, 0, z  );
      v' <@ S.verify(x, m, 1, z' );
      v'' <@ S.verify(x,m, 2, z'');
        
      return (v /\ v' /\ v'') => r;
    }
  }.

  module type Decider = {
    proc distinguish(x: statement, c :message,
    e : int, t: response) : bool
  }.

  module SHVZK (S: SigmaScheme,
  A: SigmaAlgorithms, D: Decider) = {
    proc real(h : statement, w : witness, e : int) = {
      var c, s, t ,b;
      (c,s) <@ S.commit(h,w);
      t <@ S.respond((h,w),(c,s),e);
      b <@ D.distinguish(h,c,e,t);
        return b;
    }

   proc simulate(h : statement, e : int) = {
      var c, t, b;
      
      (c,t) <@ A.simulate(h,e);
        b <@ D.distinguish(h,c,e,t);

      return b;
    }
  }.

end SigmaProtocol.
