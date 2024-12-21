require import Distr MLWE AllCore.

import M.

(* We use an axiomisied commitment scheme as part of the subsquent zero-knowledge proofs *)
(* JKPT12 calls for a perfectly binding commitment scheme which we axiomitise as follows based on the
standard Commitment with the EasyCrypt core libaries.
The most notable changes are that the commitment scheme is perfectly binding and that we allow
the adversary access to auxiliary global information (which does not depend on the coin flip) *)

theory CommitmentProtocol.
  type key.
  type commitment.
  type message.
  type opening.
  type commit_coin. (* random coin used during commits *)
  type aux.

  op keygen : key distr.
  op commit_rand : commit_coin distr.
  axiom commit_rand_uf : is_funiform commit_rand.
  axiom commit_rand_ll : is_lossless commit_rand.
  axiom keygen_ll : is_lossless keygen.
  
  op commit : key -> message -> commit_coin -> (commitment*opening).
  op verify : key -> message -> (commitment*opening) -> bool.
  (* We assume the scheme is perfectly correct this could of course be degraded *)
  axiom commit_verify_correct k m r : verify k m (commit k m r).
  axiom commit_verify_sound k m m' c d d' : (* We have perfect binding *)
  verify k m (c,d) => verify k m' (c,d') => m = m'.

  lemma commit_message_eq k m m' r :
    m = m' => (commit k m r).`1 = (commit k m' r).`1.
  proof.
    move => h. rewrite h. trivial.
  qed.
  
  lemma commit_open_eq k m m' r :
    m = m' => (commit k m r).`2 = (commit k m' r).`2.
  proof.
    move => h. rewrite h. trivial.
  qed.
  
  
  module type Unhider = {
    proc choose(x: key, a : aux) : (message * message) * (message * message)
    proc guess(c: commitment*commitment, a : aux) : bool
  }.

  (* The left right hiding exp with aux data and commitments to a pair of messengers *)
  module HidingExperimentL (U:Unhider) = {
    proc main(a : aux) : bool = {
      var b', m0, m1, r1, r2, x, c1, c2, d1, d2;

      x        <$ keygen;
      (m0, m1) <@ U.choose(x,a);
      r1       <$ commit_rand;
      r2       <$ commit_rand;
      (c1, d1) <- commit x (m0.`1) r1;
      (c2, d2) <- commit x (m0.`2) r2;
      b'       <@ U.guess((c1,c2),a);

      return b';
    }
  }.
  
    module HidingExperimentR (U:Unhider) = {
    proc main(a : aux) : bool = {
      var b', m0, m1, r1, r2, x, c1, c2, d1, d2;

      x        <$ keygen;
      (m0, m1) <@ U.choose(x,a);
      r1       <$ commit_rand;
      r2       <$ commit_rand;
      (c1, d1) <- commit x (m1.`1) r1;
      (c2, d2) <- commit x (m1.`2) r2;
      b'       <@ U.guess((c1,c2),a);

      return b';
    }
  }.
end CommitmentProtocol.
