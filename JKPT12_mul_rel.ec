require import AllCore Distr DInterval  IntDiv List Perms.

require (*--*) Commitment_aux.

require (*--*) SigmaProtocol3.
require (*--*) MLWE.

import MLWE.
import M.

require JKPT12_com.
import JKPT12_com.

  (* The basic logic in the sigma protocol formalised in this file is similar
  to the previous two formalised. However, the complexity of the protocol causes
  issues with various EasyCrypt tatics *)

 (* Meta operatios to simplfy presentation *)
type vector4     = vector*vector*vector*vector.
type list4       = int list*int list*int list*int list.

(* We need some new sampling *)
op f_sample : (vector -> vector -> vector) distr.

op R_sample : vector -> vector -> vector -> vector -> vector -> vector -> matrix distr.
axiom R_sample_eq : forall v1 v2 v3 v'1 v'2 v'3 m, m \in R_sample v1 v2 v3 v'1 v'2 v'3 =>
v1 = m*^v'1 /\ v2 = m*^v'2 /\ v3 = m*^v'3.
axiom R_sample_ll : forall q w e r t y, weight (R_sample q w e r t y) = 1%r.
axiom R_sample_size v1 v2 v3 v'1 v'2 v'3 m : m \in (R_sample v1 v2 v3 v'1 v'2 v'3) => size  m = (v, 4*v).
lemma R_sample_row v1 v2 v3 v'1 v'2 v'3 m : m \in (R_sample v1 v2 v3 v'1 v'2 v'3) => rows m = v.
    smt(@MLWE.M R_sample_size).
qed.    
lemma R_sample_col v1 v2 v3 v'1 v'2 v'3 m : m \in (R_sample v1 v2 v3 v'1 v'2 v'3) => cols m = 4*v.
    smt(@MLWE.M R_sample_size).
qed.
  
(* WARNING - the following axioms hide a computational the xLPN problem *)
op R_sample2 : vector4 -> vector4 -> vector4 -> vector -> vector -> vector -> matrix distr.
axiom R_sample_equiv : forall v1_1 v2_1 v3_1 v1_2 v2_2 v3_2 v'1 v'2 v'3 x,
  mu1 (R_sample v1_1 v2_1 v3_1 v'1 v'2 v'3) x =
  mu1 (R_sample2 v1_2 v2_2 v3_2 v'1 v'2 v'3) x.
axiom R_sample_equiv2 : forall v1_1 v2_1 v3_1 v1_2 v2_2 v3_2 v'1 v'2 v'3 x,
x \in R_sample2 v1_1 v2_1 v3_1 v'1 v'2 v'3 =>
x \in R_sample v1_2 v2_2 v3_2 v'1 v'2 v'3.

op size_v4 (w : vector4)= (size w.`1 = v /\ size w.`2 = v /\ size w.`3 = v /\ size w.`4 = v).
op size_l4 (w : vector4) = (size w.`1 = l /\ size w.`2 = l /\ size w.`3 = l /\ size w.`4 = l).
op size_k4 (w : vector4) = (size w.`1 = k /\ size w.`2 = k /\ size w.`3 = k /\ size w.`4 = k).

op zerov4 = (zerov v, zerov v, zerov v, zerov v).
op zerol4 = (zerov l, zerov l, zerov l, zerov l).
op zerok4 = (zerov k, zerov k, zerov k, zerov k).
abbrev (-) (v v' : vector4) = (v.`1 - v'.`1, v.`2 - v'.`2, v.`3 - v'.`3, v.`4 - v'.`4).
op addv4 (v v' : vector4) : vector4 = (v.`1 + v'.`1, v.`2 + v'.`2, v.`3 + v'.`3, v.`4 + v'.`4).

op dRl4 : (vector*vector*vector*vector) distr.
axiom dRl4_ll : is_lossless dRl4.
axiom dRl4_size : forall x, x \in dRl4 => size x.`1 = l /\ size x.`2 = l /\ size x.`3 = l /\ size x.`4 = l.
lemma dRl4_l4 :  forall x, x \in dRl4 => size_l4 x.
  move => x h. smt(dRl4_size).
qed.
  
op dRv4 : (vector*vector*vector*vector) distr.
axiom dRv4_ll : is_lossless dRv4.
axiom dRv4_size : forall x, x \in dRv4 => size x.`1 = v /\ size x.`2 = v /\ size x.`3 = v /\ size x.`4 = v.
lemma dRv4_v4 : forall x, x \in dRv4 => size_v4 x.
  move => x h. smt(dRv4_size).
qed.
axiom dRmu1_v4 : forall (v v' : vector4),
    size_v4 v => size_v4 v' =>
    mu1 dRv4 v =
    mu1 dRv4 (addv4 v v').
axiom dRin_v4 : forall (v : vector4),
    size_v4 v =>
    v \in dRv4.
    
op dRk4 : (vector*vector*vector*vector) distr.
axiom dRk4_ll : is_lossless dRk4.
axiom dRk4_size : forall x, x \in dRk4 => size x.`1 = k /\ size x.`2 = k /\ size x.`3 = k /\ size x.`4 = k.
lemma dRk4_k4 : forall x, x \in dRk4 => size_k4 x.
  move => x h. smt(dRk4_size).
qed.

lemma size_addv4 v1 v2 : size_v4 v1 => size_v4 v2 => size_v4 (addv4 v1 v2).
 proof.
  move => @/size_v4  h h' @/addv4. simplify.  smt(@MLWE.M).
qed.

 lemma size_addl4 v1 v2 : size_l4 v1 => size_l4 v2 => size_l4 (addv4 v1 v2).
 proof.
  move => @/size_l4  h h' @/addv4. simplify. smt(@MLWE.M).
qed.

op dW4 : (vector4) distr.
axiom dW4_def: forall x, x \in dW4 => x.`1 \in chi /\ x.`2 \in chi /\ x.`3 \in chi /\ x.`4 \in chi.
axiom dW4_ll : is_lossless dW4.
lemma dW4size  : forall x, x \in dW4 => size x.`1 = k /\ size x.`2 = k /\ size x.`3 = k /\
    size x.`4 = k.
proof.
  move => x h. apply dW4_def in h. smt(chi_k).
qed.

op checkW4 (v v' : vector4) : bool =
  checkW (v.`1 - v'.`1) /\ checkW (v.`2 - v'.`2) /\ checkW (v.`3 - v'.`3) /\ checkW (v.`4 - v'.`4).

op perm4 : (list4) distr.
axiom perm4_ll : is_lossless perm4.

op isPerm4 (x : list4) : bool = isPerm x.`1 /\ isPerm x.`2 /\ isPerm x.`3 /\ isPerm x.`4.
axiom samplePerm4_def : forall x, x\in perm4 => isPerm4 x.

op subv4 m = (subv m 0 v, subv m v (2*v), subv m (2*v) (3*v), subv m (3*v) (4*v)).
op subl4 r = (subv r 0 l, subv r l (2*l), subv r (2*l) (3*l), subv r (3*l) (4*l)).

lemma subv4_v4 v : size_v4 (subv4 v).
proof.
  move => @/subv4. simplify. smt(@MLWE.M gt0_v).   
qed.

lemma subv4_s1 v1 : size (subv4 v1).`1 = v.
proof.
  smt(subv4_v4).  
qed.

lemma subv4_s2 v1 : size (subv4 v1).`2 = v.
proof.
  smt(subv4_v4).  
qed.

lemma subv4_s3 v1 : size (subv4 v1).`3 = v.
proof.
  smt(subv4_v4).  
qed.


lemma subv4_s4 v1 : size (subv4 v1).`4 = v.
proof.
  smt(subv4_v4).  
qed.

lemma subl4_l4 v : size_l4 (subl4 v).
proof.
  move => @/subl4. simplify. smt(@MLWE.M gt0_l).   
qed.

lemma subl4_s1 v1 : size (subl4 v1).`1 = l.
proof.
  smt(subl4_l4).  
qed.

lemma subl4_s2 v1 : size (subl4 v1).`2 = l.
proof.
  smt(subl4_l4).  
qed.

lemma subl4_s3 v1 : size (subl4 v1).`3 = l.
proof.
  smt(subl4_l4).  
qed.

lemma subl4_s4 v1 : size (subl4 v1).`4 = l.
proof.
  smt(subl4_l4).  
qed.

lemma subv_cat4_2 (m : vector) j :  0 < j => size m = 4*j =>
    (subv m 0 j || subv m j (2 * j) || subv m (2 * j) (3 * j) || subv m (3 * j) (4 * j)) = m.
proof.
  move => h h1. apply eq_vectorP. split. smt(@MLWE.M).
  move => i hi. rewrite !get_catv. rewrite !size_subv.
  case (i < max 0 (j - 0)); move => h0. smt(@MLWE.M). case (i - max 0 (j - 0) < max 0 (2 * j - j) ); move => h2.
  smt(@MLWE.M). case (i - max 0 (j - 0) - max 0 (2 * j - j) < max 0 (3 * j - 2 * j)); move => h3. smt(@MLWE.M).  smt(@MLWE.M).
qed.

lemma subv4_1 (m : vector4) : size m.`1 = v => (subv4 (m.`1 || m.`2 || m.`3 || m.`4)).`1 = m.`1.
    smt(@MLWE.M).
qed.

lemma subv4_2 (m : vector4) : size m.`1 = v => size m.`2 = v => (subv4 (m.`1 || m.`2 || m.`3 || m.`4)).`2 = m.`2.
    move => @/subv4 h0 h1. simplify. apply eq_vectorP. split. smt(@MLWE.M). move => i h2. rewrite get_subv.
    rewrite size_subv in h2. smt(). rewrite get_catv. rewrite h0. have : !(i + v < v). smt(). move => h3. rewrite h3.
    simplify. rewrite get_catv. have : i + v - v < size m.`2. smt(@MLWE.M). move => h4. rewrite h4. simplify. smt().
qed.
  
lemma subv4_3 (m : vector4) : size m.`1 = v => size m.`2 = v => size m.`3 = v =>
    (subv4 (m.`1 || m.`2 || m.`3 || m.`4)).`3 = m.`3.
proof.
  move => h0 h1 h2  @/subv4. simplify.  apply eq_vectorP. split. smt(@MLWE.M). move => i h4. rewrite get_subv.
  smt(@MLWE.M). rewrite get_catv. have : !(i + 2 * v < size m.`1). smt(). move => h5. rewrite h5. simplify.
  rewrite get_catv. have : !(i + 2 * v - size m.`1 < size m.`2). smt(). move => h6. rewrite h6. simplify.
  rewrite get_catv. have : (i + 2 * v - size m.`1 - size m.`2 < size m.`3). smt(@MLWE.M). move => h7. rewrite h7. simplify.
  smt().
qed.
  
lemma subv4_4 (m : vector4) : size m.`1 = v => size m.`2 = v => size m.`3 = v => size m.`4 = v =>
    (subv4 (m.`1 || m.`2 || m.`3 || m.`4)).`4 = m.`4.
proof.    
  move => h0 h1 h2 h3 @/subv4. simplify.  apply eq_vectorP. split. smt(@MLWE.M). move => i h4. rewrite get_subv.
  smt(@MLWE.M). rewrite get_catv. have : !(i + 3 * v < size m.`1). smt(). move => h5. rewrite h5. simplify.
  rewrite get_catv. have : !(i + 3 * v - size m.`1 < size m.`2). smt(). move => h6. rewrite h6. simplify.
  rewrite get_catv. have : !(i + 3 * v - size m.`1 - size m.`2 < size m.`3). smt(). move => h7. rewrite h7. simplify.
  smt().
qed.

lemma size_addv4_1 v1 v2 : v1 \in dRv4 => v2 \in dvector dR (4 * v) =>
    size (addv4 v1 (subv4 v2)).`1 = v.
proof.
  move => h1 h2. apply dRv4_size in h1. smt(size_addv4 subv4_v4 ).
qed.

lemma size_addv4_2 v1 v2 : v1 \in dRv4 => v2 \in dvector dR (4 * v) =>
    size (addv4 v1 (subv4 v2)).`2 = v.
proof.
  move => h1 h2. apply dRv4_size in h1. smt(size_addv4 subv4_v4 ).
qed.

lemma size_addv4_3 v1 v2 : v1 \in dRv4 => v2 \in dvector dR (4 * v) =>
    size (addv4 v1 (subv4 v2)).`3 = v.
proof.
  move => h1 h2. apply dRv4_size in h1. smt(size_addv4 subv4_v4 ).
qed.

lemma size_addv4_4 v1 v2 : v1 \in dRv4 => v2 \in dvector dR (4 * v) =>
    size (addv4 v1 (subv4 v2)).`4 = v.
proof.
  move => h1 h2. apply dRv4_size in h1. smt(size_addv4 subv4_v4 ).
qed.

lemma size_addl4_1 v1 v2 : v1 \in dRl4 => v2 \in dvector dR (4 * l) =>
    size (addv4 v1 (subl4 v2)).`1 = l.
proof.
  move => h1 h2. apply dRl4_size in h1. smt(size_addl4 subl4_l4).
qed.

lemma size_addl4_2 v1 v2 : v1 \in dRl4 => v2 \in dvector dR (4 * l) =>
    size (addv4 v1 (subl4 v2)).`2 = l.
proof.
  move => h1 h2. apply dRl4_size in h1. smt(size_addl4 subl4_l4).
qed.

lemma size_addl4_3 v1 v2 : v1 \in dRl4 => v2 \in dvector dR (4 * l) =>
    size (addv4 v1 (subl4 v2)).`3 = l.
proof.
  move => h1 h2. apply dRl4_size in h1. smt(size_addl4 subl4_l4).
qed.

lemma size_addl4_4 v1 v2 : v1 \in dRl4 => v2 \in dvector dR (4 * l) =>
    size (addv4 v1 (subl4 v2)).`4 = l.
proof.
  move => h1 h2. apply dRl4_size in h1. smt(size_addl4 subl4_l4).
qed.

op JKPT12commit4 (a : matrix) (m : vector) (r : vector) (e : vector4) : vector4 =
  let m' = subv4 m in
  let r' = subl4 r in
   (a *^ (r'.`1 ||  m'.`1) + e.`1, a *^ (r'.`2 || m'.`2) + e.`2,
     a *^ (r'.`3 ||  m'.`3) + e.`3, a *^ (r'.`4 || m'.`4) + e.`4).

op checkWComm (a : matrix) (y r m : vector4) : bool.
axiom checkWComm_def: forall a (y r m : vector4), checkWComm a y r m <=>
  checkW (a *^ (r.`1 || m.`1) - y.`1) /\ checkW (a *^ (r.`2 || m.`2) - y.`2) /\
 checkW (a *^ (r.`3 || m.`3) - y.`3) /\ checkW (a *^ (r.`4 || m.`4) - y.`4).

  (* The axiom below follows from pedersen_computational_binding in JKPT12_com *)
axiom JKPT12_sound4 a y r m r' m' : checkWComm a y r m => checkWComm a y r' m' => m = m'.

   
lemma JKPT12commit4_corr a m r e : rows a = k => e \in dW4 => checkWComm a (JKPT12commit4 a m r e) (subl4 r) (subv4 m).
proof.
  move => h0 h @/JKPT12commit4. have : e \in dW4. trivial. move => h1. apply dW4_def in h. apply dW4size in h1.
  rewrite checkWComm_def. simplify. do! split.
  rewrite oppvD. rewrite addvA. rewrite addvN. rewrite lin_add0v. smt(@MLWE.M gt0_k). rewrite bRing. smt(chi_weight).
  rewrite oppvD. rewrite addvA. rewrite addvN. rewrite lin_add0v. smt(@MLWE.M gt0_k). rewrite bRing. smt(chi_weight).
  rewrite oppvD. rewrite addvA. rewrite addvN. rewrite lin_add0v. smt(@MLWE.M gt0_k). rewrite bRing. smt(chi_weight).
  rewrite oppvD. rewrite addvA. rewrite addvN. rewrite lin_add0v. smt(@MLWE.M gt0_k). rewrite bRing. smt(chi_weight).
qed.

lemma JKPT12commit4_size a m r e: size_k4 e => rows a = k => size_k4 (JKPT12commit4 a m r e).
   move => h0 h1 @/JKPT12commit4. split. simplify.
  rewrite size_addv. rewrite size_mulmxv. smt(). split. simplify.
  rewrite size_addv. rewrite size_mulmxv. smt(). split. simplify.
  rewrite size_addv. rewrite size_mulmxv. smt(). simplify.
  rewrite size_addv. rewrite size_mulmxv. smt().
  qed.

lemma JKPT12commit4_size_1 a m r e: size_k4 e => rows a = k => size (JKPT12commit4 a m r e).`1 = k.
  smt(JKPT12commit4_size).
  qed.

  lemma JKPT12commit4_size_2 a m r e: size_k4 e => rows a = k => size (JKPT12commit4 a m r e).`2 = k.
  smt(JKPT12commit4_size).
    qed.

    lemma JKPT12commit4_size_3 a m r e: size_k4 e => rows a = k => size (JKPT12commit4 a m r e).`3 = k.
  smt(JKPT12commit4_size).
      qed.

      lemma JKPT12commit4_size_4 a m r e: size_k4 e => rows a = k => size (JKPT12commit4 a m r e).`4 = k.
  smt(JKPT12commit4_size).
qed.  
  
op t0_perm4 (pi :  list4) : vector4 =
 (permToVector pi.`1, permToVector pi.`2, permToVector pi.`3, permToVector pi.`4).
op t0_4 m (u v f : vector4) =
   (m *^ (catv u.`1 v.`1) + f.`1,m *^ (catv u.`2 v.`2) + f.`2,m *^ (catv u.`3 v.`3) + f.`3,m *^ (catv u.`4 v.`4) + f.`4).
op t1_4 (f : vector4)(pi : list4) =
   (permVector (- f.`1) pi.`1, permVector (- f.`2) pi.`2, permVector (- f.`3) pi.`3, permVector (- f.`4) pi.`4).
op t2_4 (f e : vector4) (pi :  list4) =
   (permVector (-(f.`1 + e.`1)) pi.`1, permVector (-(f.`2 + e.`2)) pi.`2,
     permVector (-(f.`3 + e.`3)) pi.`3, permVector (-(f.`4 + e.`4)) pi.`4).

lemma t0_4_k4 m u v f : rows m = k => size_k4 f => size_k4 (t0_4 m u v f).
    move => h0 h1 @/t0_4. smt(gt0_k @MLWE.M).
  qed.

  lemma t0_4_k4_1 m u v f : rows m = k => size_k4 f => size (t0_4 m u v f).`1 = k.
    move => h0 h1 @/t0_4. smt(gt0_k @MLWE.M).
  qed.

  lemma t0_4_k4_2 m u v f : rows m = k => size_k4 f => size (t0_4 m u v f).`2 = k.
    move => h0 h1 @/t0_4. smt(gt0_k @MLWE.M).
  qed.

  lemma t0_4_k4_3 m u v f : rows m = k => size_k4 f => size (t0_4 m u v f).`3 = k.
    move => h0 h1 @/t0_4. smt(gt0_k @MLWE.M).
  qed.
    
  lemma t0_4_k4_4 m u v f : rows m = k => size_k4 f => size (t0_4 m u v f).`4 = k.
    move => h0 h1 @/t0_4. smt(gt0_k @MLWE.M).
   qed.
          
  
lemma t1_4_k4 f pi : isPerm4 pi => size_k4 (t1_4 f pi).
     smt(permVectorSize).
  qed.

lemma t1_4_k4_1 f pi : isPerm4 pi => size (t1_4 f pi).`1 = k.
     smt(permVectorSize).
  qed.

lemma t1_4_k4_2 f pi : isPerm4 pi => size (t1_4 f pi).`2 = k.
     smt(permVectorSize).
qed.

lemma t1_4_k4_3 f pi : isPerm4 pi => size (t1_4 f pi).`3 = k.
     smt(permVectorSize).
qed.
    
lemma t1_4_k4_4 f pi : isPerm4 pi => size (t1_4 f pi).`4 = k.
     smt(permVectorSize).
qed.
  
lemma t2_4_k4 f e pi    : isPerm4 pi => size_k4 (t2_4 f e pi).
     smt(permVectorSize).
  qed.

lemma t2_4_k4_1 f e pi    : isPerm4 pi => size (t2_4 f e pi).`1 = k.
     smt(permVectorSize).
qed.  

lemma t2_4_k4_2 f e pi    : isPerm4 pi => size (t2_4 f e pi).`2 = k.
     smt(permVectorSize).
  qed.

lemma t2_4_k4_3 f e pi    : isPerm4 pi => size (t2_4 f e pi).`3 = k.
     smt(permVectorSize).
  qed.

lemma t2_4_k4_4 f e pi    : isPerm4 pi => size (t2_4 f e pi).`4 = k.
     smt(permVectorSize).
qed.  
 
lemma permToVectorInj4 p p' : t0_perm4 p = t0_perm4 p' => p = p'.
  move => h. smt(permToVectorInj).     
qed.
  
op v_calc r (v_j : vector4) = (subm r 0 v 0 v) *^ v_j.`1 + (subm r 0 v v (2*v)) *^ v_j.`2 +
(subm r 0 v(2*v) (3*v)) *^ v_j.`3 + (subm r 0 v (3*v) (4*v)) *^ v_j.`4.

lemma size_v_calc r v_j : size (v_calc r v_j) = v.
proof.
  move => @/v_calc. rewrite !size_addv. rewrite !size_mulmxv. rewrite !rows_subm. smt(gt0_v).
qed.

lemma subv_cat4 (m : vector) j : 0 < j => size m = 4*j =>
    (((subv m 0 j || subv m j (2 * j)) || subv m (2 * j) (3 * j)) || subv m (3 * j) (4 * j)) = m.
proof.
  move => h0 h1. apply eq_vectorP. split. smt(@MLWE.M).
  move => i hi. rewrite !get_catv. rewrite !size_catv. rewrite !size_subv.
  case (i <  max 0 (j - 0) + max 0 (2 * j - j) + max 0 (3 * j - 2 * j)); move => h2.
  case (i < max 0 (j - 0) + max 0 (2 * j - j)); move => h3.
  case (i < max 0 (j - 0)); move => h4.  rewrite get_subv. smt(). smt(). rewrite get_subv. smt(). smt().
   rewrite get_subv. smt(). smt().  rewrite get_subv. smt(@MLWE.M). smt().
qed.
    
lemma subm_row (r : matrix) (i j j' : int) : size r = (v,4*v) => j'-j = v => 0 <= i && i < v =>
    row (subm r 0 v j j') i = subv (row r i) j j'.
proof.
  move => h0 h1 h2. apply eq_vectorP. split. rewrite !size_row. rewrite cols_subm. smt(@MLWE.M).
  move => i0 hi0. simplify. rewrite get_subm. smt(@Int). smt(@MLWE.M).
  rewrite get_subv. smt(@MLWE.M). simplify. trivial. 
qed. 
  
lemma subm_mulmx (r : matrix) (m : vector) : size r = (v,4*v) => size m = 4*v => 
    subm r 0 v 0 v *^ (subv4 m).`1 + subm r 0 v v (2 * v) *^ (subv4 m).`2 +
    subm r 0 v (2 * v) (3 * v) *^ (subv4 m).`3 + subm r 0 v (3 * v) (4 * v) *^ (subv4 m).`4 = r *^ m.
proof.
  move => h0 h1 @/subv4. simplify. apply eq_vectorP. split.
  rewrite !size_addv. rewrite !size_mulmxv. rewrite !rows_subm. smt().
  move => i hi. rewrite !get_addv. rewrite !get_mulmxv. rewrite subm_row; trivial. smt(@MLWE.M).
  rewrite subm_row; trivial. smt(@MLWE.M). smt(@MLWE.M). rewrite subm_row; trivial. smt(@MLWE.M). smt(@MLWE.M).
  rewrite subm_row; trivial. smt(@MLWE.M). smt(@MLWE.M). rewrite -dotp_catv. smt(@MLWE.M). rewrite -dotp_catv. smt(@MLWE.M).
  rewrite -dotp_catv. smt(@MLWE.M). rewrite (subv_cat4). apply gt0_v. smt(@MLWE.M). rewrite (subv_cat4). apply gt0_v. smt(@MLWE.M).
  trivial.
qed.
    
op compact (v : vector4) : vector = v.`1 || v.`2 || v.`3 || v.`4.
lemma compact_bij_v v v' : size_v4 v => size_v4 v' => compact v = compact v' <=> v = v'. 
proof.
  move => h0 h1. split; smt(@MLWE.M).
qed.
lemma compact_bij_k v v' : size_k4 v => size_k4 v' => compact v = compact v' <=> v = v'. 
proof.
  move => h0 h1. split; smt(@MLWE.M).
qed.

lemma compact_neg_v v v' : size_v4 v => size_v4 v' => compact v - compact v' = compact (v - v'). 
   move => h0 h1 @/compact. simplify. smt(@MLWE.M).
qed.

lemma compact_neg_l v v' : size_l4 v => size_l4 v' => compact v - compact v' = compact (v - v'). 
   move => h0 h1 @/compact. simplify. smt(@MLWE.M).
qed.  
  
lemma compact_subv4 (w : vector) : size w = 4*v => compact (subv4 w) = w.
  move => h @/compact @/subv4. simplify. apply subv_cat4_2. apply gt0_v. trivial.
  qed.
  
lemma v_calc_mat (r : matrix) (m : vector4) : size r = (v,4*v) => size_v4 m => v_calc r m = r *^ (compact m).
proof.
   move => h0 h1  @/v_calc @/compact. rewrite -(subm_mulmx r). trivial. smt(@MLWE.M).
  rewrite subv4_1. smt(). rewrite subv4_2. smt(). smt(). rewrite subv4_3. smt(). smt(). smt(). rewrite subv4_4; smt().
qed.

lemma v_calc_addv4 v v' v'' : v_calc v (addv4 v' v'') = v_calc v v' + v_calc v v''.
proof.
  move => @/v_calc @/addv4. simplify. rewrite !mulmxvDr. rewrite !addvA. congr. rewrite addvC. rewrite !addvA.
  congr. rewrite addvC. rewrite !addvA. congr. rewrite addvC. rewrite !addvA. congr.
  rewrite addvC. rewrite !addvA. congr. 
qed.

lemma v_calc_swap_1 m1 m2 m3 mTilde1 mTilde2 mTilde3 r : r \in R_sample m1 m2 m3 mTilde1 mTilde2 mTilde3 => 
    size mTilde1 = 4 * v => v_calc r (subv4 mTilde1) = m1.
proof.
  move => h0 h1 @/v_calc. have : size r = (v, 4*v). smt(R_sample_size). move =>h. apply R_sample_eq in h0. rewrite h0.
 apply subm_mulmx. smt(). smt(). 
qed.

lemma v_calc_swap_2 m1 m2 m3 mTilde1 mTilde2 mTilde3 r : r \in R_sample m1 m2 m3 mTilde1 mTilde2 mTilde3 => 
    size mTilde2 = 4 * v => v_calc r (subv4 mTilde2) = m2.
proof.
  move => h0 h1 @/v_calc. have : size r = (v, 4*v). smt(R_sample_size). move =>h. apply R_sample_eq in h0. rewrite h0.
 apply subm_mulmx. smt(). smt(). 
qed.

lemma v_calc_swap_3 m1 m2 m3 mTilde1 mTilde2 mTilde3 r : r \in R_sample m1 m2 m3 mTilde1 mTilde2 mTilde3 => 
    size mTilde3 = 4 * v => v_calc r (subv4 mTilde3) = m3.
proof.
  move => h0 h1 @/v_calc. have : size r = (v, 4*v). smt(R_sample_size). move =>h. apply R_sample_eq in h0. rewrite h0.
 apply subm_mulmx. smt(). smt(). 
qed.


op e0_check(a :matrix) (u v t0 t1 : vector4)(pi : list4) : bool.
axiom e0_check_def : forall a u v t0 t1 pi, e0_check a u v t0 t1 pi 
 <=> a *^ (u.`1 || v.`1)  = (t0.`1 + permVector t1.`1 (invPerm pi.`1)) /\
  a *^ (u.`2 || v.`2)  = (t0.`2 + permVector t1.`2 (invPerm pi.`2)) /\
  a *^ (u.`3 || v.`3)  = (t0.`3 + permVector t1.`3 (invPerm pi.`3)) /\
  a *^ (u.`4 || v.`4)  = (t0.`4 + permVector t1.`4 (invPerm pi.`4)).

op e1_check (a : matrix) (u v t0 t1 y : vector4)(pi : list4) : bool.
axiom e1_check_def : forall a u v t0 t1 y pi, e1_check a u v t0 t1 y pi
<=> a *^ (u.`1 || v.`1) = (t0.`1 +  (permVector t1.`1 (invPerm pi.`1))) + y.`1 /\
  a *^ (u.`2 || v.`2) = (t0.`2 +  (permVector t1.`2 (invPerm pi.`2))) + y.`2 /\
  a *^ (u.`3 || v.`3) = (t0.`3 +  (permVector t1.`3 (invPerm pi.`3))) + y.`3 /\
  a *^ (u.`4 || v.`4) = (t0.`4 +  (permVector t1.`4 (invPerm pi.`4))) + y.`4.

lemma e_check_simp_sub (a b b' c : vector) pi: isPerm pi => size b = k => size b' = k => size a = k =>
   c + (permVector (b-b') pi) = a + (permVector b pi) + c + (a + (permVector b' pi)).
 proof.
   move => h0 h1 h2 h3. rewrite -(bRing (a + permVector b' pi)). rewrite (addvC (a + _)). rewrite oppvD. rewrite -addvA.
   congr. trivial. rewrite -permVectorAdd. trivial. smt(@List gt0_k). rewrite bRing. smt(@List gt0_k).
   rewrite (addvC a). -rewrite addvA. congr. rewrite -addvA. rewrite addvN. rewrite lin_addv0.
   smt(@List gt0_k permVectorSize). trivial. rewrite permVectorOp. trivial. trivial.
qed.
    
lemma e_check_simp A (u_j v_j u'_j v'_j t0_j t10_j t11_j y : vector4) pi_j :
  size_k4 y => size_k4 t0_j => size_k4 t10_j => size_k4 t11_j => 
  isPerm4 pi_j =>  
  e1_check A u_j v_j t0_j t10_j y pi_j =>
  e0_check A u'_j v'_j t0_j t11_j pi_j =>
  y.`1 + permVector (t10_j.`1 - t11_j.`1) (invPerm pi_j.`1) = A *^ (u_j.`1 || v_j.`1) + A *^ (u'_j.`1 || v'_j.`1) /\
  y.`2 + permVector (t10_j.`2 - t11_j.`2) (invPerm pi_j.`2) = A *^ (u_j.`2 || v_j.`2) + A *^ (u'_j.`2 || v'_j.`2) /\
  y.`3 + permVector (t10_j.`3 - t11_j.`3) (invPerm pi_j.`3) = A *^ (u_j.`3 || v_j.`3) + A *^ (u'_j.`3 || v'_j.`3) /\
  y.`4 + permVector (t10_j.`4 - t11_j.`4) (invPerm pi_j.`4) = A *^ (u_j.`4 || v_j.`4) + A *^ (u'_j.`4 || v'_j.`4).  
proof.
  rewrite e0_check_def. rewrite e1_check_def. move => @/compact h2 h3 h4 h6 h7 h0 h1. simplify.
  rewrite h0. rewrite h1. rewrite h0. rewrite h1. rewrite h0. rewrite h1. rewrite h0. rewrite h1.
  split. apply e_check_simp_sub; smt(invPermPerm). split. apply e_check_simp_sub; smt(invPermPerm).
  split. apply e_check_simp_sub; smt(invPermPerm). apply e_check_simp_sub; smt(invPermPerm).
qed.

lemma e_check_simp2_sub (c a : vector): size c = size a =>
    c + a + c = a.
proof.
  move => h. pose q := c + a. rewrite -(bRing c). move => @/q. rewrite (addvC c). rewrite -addvA. rewrite addvN.
  rewrite lin_addv0. smt(). trivial.
qed.

lemma e_check_simp2 A (u_j v_j u'_j v'_j t0_j t10_j t11_j y : vector4) pi_j :
    size_k4 y => size_k4 t0_j => size_k4 t10_j => size_k4 t11_j =>
    size_v4 v_j => size_v4 v'_j => size_l4 u_j =>  size_l4 u'_j =>
    isPerm4 pi_j =>  
    e1_check A u_j v_j t0_j t10_j y pi_j =>
    e0_check A u'_j v'_j t0_j t11_j pi_j =>
    checkW4 t11_j t10_j   =>
    checkWComm A y (u_j - u'_j) (v_j - v'_j).
proof.
  rewrite !checkWComm_def. move => @/checkW4 h2 h3 h4 h6 h9 h10 h11 h12 h7 h0 h1 h8.
  rewrite !bRing. simplify. rewrite -!addv_catv. smt(). smt(). smt(). smt(). rewrite !mulmxvDr.
  rewrite -!(e_check_simp _ _ _ _ _ _ _ _ _ _ h2 h3 h4 h6 h7 h0 h1). rewrite !bRing. rewrite !bRing in h8.
  rewrite !e_check_simp2_sub. smt(permVectorSize invPermPerm). smt(permVectorSize invPermPerm). smt(permVectorSize invPermPerm).
  smt(permVectorSize invPermPerm). rewrite -!checkWPerm. apply invPermPerm. smt(). smt(@M). apply invPermPerm. smt(). smt(@M).
  apply invPermPerm. smt(). smt(@M). apply invPermPerm. smt(). smt(@M). smt(@M).
qed. 

(* commitment scheme addations *)
op matrixToVector : matrix -> vector.
axiom matrixToVectorInj m m' : matrixToVector m = matrixToVector m' => m = m'.

(* an axiomisation of full rank and at most 1 in each row *)
op validMatrix (r : matrix) : bool.
op validFunction  (f : vector -> vector -> vector) : bool.
axiom validMatrix_validFunction r (f : vector -> vector -> vector) v v' v'' : validMatrix r => validFunction f =>
  r *^v = f (r *^ v') (r *^ v'') <=> v = f v' v''.
axiom R_sample_valid : forall v1 v2 v3 v'1 v'2 v'3 x,
  x \in R_sample v1 v2 v3 v'1 v'2 v'3 => validMatrix x.

(* commitment schmeme to use in sigma protocol *)
  (* we use a commitment scheme which can commit to 4 vectors even though we
  sometimes commit to less. In such case we commit a zero vector of length zero in
  the unused slots. *)

clone import Commitment_aux as CP with
type CommitmentProtocol.aux <- (matrix * (vector*vector*vector) *
  (vector -> vector -> vector))* ((vector * vector * vector) *(vector*vector*vector))*int,
  type CommitmentProtocol.message <- vector*vector*vector*vector4*vector4*vector4*vector4.
export CommitmentProtocol.

(* Beginning sigma protocol *)
   
clone import SigmaProtocol3 as SP with
  (* matrix A and commtiment y_0, y_1, y_2, bitwiseop and key *)
  type  SigmaProtocol.statement <- matrix * (vector *  vector *  vector) * (vector -> vector -> vector),
  (* vectors r_1, r_2, r_3 and m_1, m_2, m_3 *) 
  type SigmaProtocol.witness    <- (vector * vector * vector) * (vector * vector * vector),
  type SigmaProtocol.message <-
  (key*commitment * commitment * commitment * commitment), (* c0, c1, c2, c3 *)
  
  type SigmaProtocol.secret <-
    ((vector * vector) * matrix *  (* m1, m2, r, dr *)
    (vector * vector * vector) * (vector4 * vector4 * vector4) * (* (r1,r2,r3),(e1_j,e2_j,e3_j) *)
    (int list * int list * int list) * (list4 * list4 * list4) * (*(pi1,pi2,pi3),(pi1_j,pi2_j,pi3_j) *)
    (vector * vector * vector) * (*  (catv u1 v1,catv u2 v2,catv u3 v3) *)
    (* (t11,t12,t13),(t21,t22,t23),(t31,t32,t33) *)
    (vector * vector * vector) *  (vector * vector * vector) *  (vector * vector * vector) * 
    opening * opening * opening * opening * (* d0 d1 d2 d3 *)
    (vector4 * vector4 * vector4) * (vector4 * vector4 * vector4) * (* (t11_j,t12_j,t13_j),(t21_j,t22_j,t23_j) *)
    (vector4 * vector4 * vector4) *
     (vector4 * vector4 * vector4 * vector4 * vector4 * vector4)),
  
  type SigmaProtocol.response <-
   (*  (pi1,   t10,     t11,     pi1_j,  t10_j,    t11_j,          y1,    *)   
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) * matrix *
    (* d10, d11, d12, dr, dTilde0  *)opening * opening * opening,
   
  op SigmaProtocol.R = fun (m : matrix * (vector *  vector *  vector)  * (vector -> vector -> vector))
    (w : (vector * vector * vector) * (vector * vector * vector)) =>
      (* Valid commitments *)  
      checkW  (m.`2.`1 - (m.`1 *^ (catv w.`2.`1 w.`1.`1))) /\
      checkW  (m.`2.`2 - (m.`1 *^ (catv w.`2.`2 w.`1.`2))) /\
      checkW  (m.`2.`3 - (m.`1 *^ (catv w.`2.`3 w.`1.`3))) /\
      (* Messages constraint *)
      w.`1.`3 = m.`3 w.`1.`1 w.`1.`2 /\
      (* Commitments of expected size *)
      size m.`2.`1 = rows m.`1 /\ size m.`2.`2 = rows m.`1 /\  size m.`2.`3 = rows m.`1 /\
      (* Matrix of expected size *)
      rows m.`1 = k /\ l + v = cols m.`1 /\
      (* Messages and randomness of expected size *)
      size w.`2.`1 = l /\  size w.`1.`1 = v /\
      size w.`2.`2 = l /\  size w.`1.`2 = v /\
      size w.`2.`3 = l /\  size w.`1.`3 = v /\
      (* operation is bitwise *)
      (forall x y, size (m.`3 x y) = 4 * v) /\
      (forall (x1 y1 x2 y2 : vector), m.`3 (x1 + x2) (y1 + y2) = m.`3 x1 y1 + m.`3 x2 y2) /\
      validFunction m.`3, 
    
  op SigmaProtocol.de = (duniform (range 0 3)).
  export SigmaProtocol.

  module MultiRelProt  : SigmaScheme ={
  proc gen() : (matrix*(vector*vector*vector)*(vector -> vector -> vector))
    *((vector*vector*vector)*(vector*vector*vector)) = {
     var a, m1, m2, m3, c1, c2, c3, d1, d2, d3,  f;
    a <@ JKPT12.gen();
    m1 <$ dvector dR v;
    m2 <$ dvector dR v;
    f <$ f_sample;  
    m3 <- f m1 m2;
    (c1, d1) <@ JKPT12.commit(a,m1);
    (c2, d2) <@ JKPT12.commit(a,m2);
    (c3, d3) <@ JKPT12.commit(a,m3);
    return ((a,(c1,c2,c3),f),((m1,m2,m3),(d1,d2,d3)));
  }

  proc commit (h: matrix*(vector*vector*vector)*(vector->vector->vector),
      w: (vector*vector*vector)*(vector*vector*vector)) :
    (key*commitment * commitment * commitment * commitment) *
    ((vector * vector) * matrix  *  (* m1, m2, r, dr *)
    (vector * vector * vector) * (vector4 * vector4 * vector4) * (* (r1,r2,r3),(e1_j,e2_j,e3_j) *)
    (int list * int list * int list) * (list4 * list4 * list4) * (*(pi1,pi2,pi3),(pi1_j,pi2_j,pi3_j) *)
    (vector * vector * vector) * (*  (catv u1 v1,catv u2 v2,catv u3 v3) *)
    (* (t11,t12,t13),(t21,t22,t23),(t31,t32,t33) *)
    (vector * vector * vector) *  (vector * vector * vector) *  (vector * vector * vector) * 
    opening * opening * opening * opening * (* d0 d1 d2 d3 *)
    (vector4 * vector4 * vector4) * (vector4 * vector4 * vector4) * (* (t11_j,t12_j,t13_j),(t21_j,t22_j,t23_j) *)
    (vector4 * vector4 * vector4) * 
     (vector4 * vector4 * vector4 * vector4 * vector4 * vector4))
    ={
      var pi1, pi2, pi3, pi1_j, pi2_j, pi3_j, m1, m2, m3, r1, r2, r3, f1, f2, f3, f1_j, f2_j, f3_j, r, y1, y2, y3;
      var key, e1, e2, e3, e1_j, e2_j, e3_j, t11, t12, t13, t21, t22, t23, t31, t32, t33;
      var t11_j, t12_j, t13_j, t21_j, t22_j, t23_j, t31_j, t32_j, t33_j;
      var c0, c1, c2, c3, d0, d1, d2, d3, rr0, rr1, rr2, rr3;
      var u1, u2, u3, v1, v2, v3, u1_j, u2_j, u3_j, v1_j, v2_j, v3_j;

      key <$ keygen;
      
      (* Sample the vectors *)
      m1 <$ dvector dR (4*v);
      m2 <$ dvector dR (4*v);
      (* and computer v3 *)
      m3 <- h.`3 m1 m2;
      
      v1_j <$ dRv4;
      v2_j <$ dRv4;
      v3_j <$ dRv4;
      
      r <$ R_sample w.`1.`1 w.`1.`2 w.`1.`3 m1 m2 m3;

      v1 <- v_calc r v1_j;
      v2 <- v_calc r v2_j;
      v3 <- v_calc r v3_j;

      (* other vector info *)
      r1 <$ dvector dR (4*l);
      r2 <$ dvector dR (4*l);
      r3 <$ dvector dR (4*l);

      (* compute the vectors to commit to *)
      e1_j <$ dW4;
      e2_j <$ dW4;
      e3_j <$ dW4;
      y1 <- JKPT12commit4 h.`1 m1 r1 e1_j;
      y2 <- JKPT12commit4 h.`1 m2 r2 e2_j;
      y3 <- JKPT12commit4 h.`1 m3 r3 e3_j;

      (* Sample the permutations *)
      pi1 <$ (duniform (allperms (range 0 k)));
      pi2 <$ (duniform (allperms (range 0 k)));
      pi3 <$ (duniform (allperms (range 0 k)));
      pi1_j <$ perm4;
      pi2_j <$ perm4;
      pi3_j <$ perm4;

      (* sample more vector *)
      u1_j <$ dRl4;
      u2_j <$ dRl4;
      u3_j <$ dRl4;
    
      u1 <$ dvector dR l;
      u2 <$ dvector dR l;
      u3 <$ dvector dR l;

      e1 <- h.`2.`1 - (h.`1 *^ (catv w.`2.`1 w.`1.`1));
      e2 <- h.`2.`2 - (h.`1 *^ (catv w.`2.`2 w.`1.`2));
      e3 <- h.`2.`3 - (h.`1 *^ (catv w.`2.`3 w.`1.`3));
    
      f1 <$ dvector dR k;
      f2 <$ dvector dR k;
      f3 <$ dvector dR k;
      f1_j <$ dRk4;
      f2_j <$ dRk4;
      f3_j <$ dRk4;  

      t11 <-  h.`1 *^ (catv u1 v1) + f1;
      t12 <- permVector (- f1) pi1;
      t13 <-  permVector (-(f1 + e1)) pi1;
    
      t21 <-  h.`1 *^ (catv u2 v2) + f2;
      t22 <- permVector (- f2) pi2;
      t23 <-  permVector (-(f2 + e2)) pi2;
    
      t31 <-  h.`1 *^ (catv u3 v3) + f3;
      t32 <- permVector (- f3) pi3;
      t33 <-  permVector (-(f3 + e3)) pi3;

      t11_j <- t0_4 h.`1 u1_j v1_j f1_j;
      t12_j <- t1_4 f1_j pi1_j;
      t13_j <- t2_4 f1_j e1_j pi1_j;
    
      t21_j <- t0_4 h.`1 u2_j v2_j f2_j;
      t22_j <- t1_4 f2_j pi2_j;
      t23_j <- t2_4 f2_j e2_j pi2_j;
    
      t31_j <- t0_4 h.`1 u3_j v3_j f3_j;
      t32_j <- t1_4 f3_j pi3_j;
      t33_j <- t2_4 f3_j e3_j pi3_j;

      
      (*C i 0 and js *)
      rr0 <$ commit_rand;
      rr1 <$ commit_rand;
      rr2 <$ commit_rand;
      rr3 <$ commit_rand;
      
      (c0, d0) <- commit key (permToVector pi1,permToVector pi2, permToVector pi3,
        t0_perm4 pi1_j, t0_perm4 pi2_j, t0_perm4 pi3_j, zerov4) rr0;

      (c1, d1) <- commit key (t11, t21, t31,  t11_j, t21_j, t31_j, (matrixToVector r, zerov 0, zerov 0, zerov 0)) rr1;

      (c2, d2) <- commit key (t12, t22, t32, t12_j, t22_j, t32_j, zerov4) rr2;

      (c3, d3) <- commit key (t13, t23, t33, t13_j, t23_j, t33_j,  (compact y1, compact y2, compact y3, zerov 0)) rr3;
      
       return ((key,c0,c1,c2,c3),
        ((m1,m2),r,(r1,r2,r3),(e1_j,e2_j,e3_j),(pi1,pi2,pi3),(pi1_j,pi2_j,pi3_j),
        (catv u1 v1,catv u2 v2,catv u3 v3),(t11,t12,t13),(t21,t22,t23),(t31,t32,t33),
        d0,d1,d2,d3,(t11_j,t12_j,t13_j),(t21_j,t22_j,t23_j),(t31_j,t32_j,t33_j),
        (u1_j,u2_j,u3_j,v1_j,v2_j,v3_j)));  
  }

  
   proc test (h: matrix*(vector*vector*vector)*(vector->vector->vector), com :
      (key*commitment * commitment * commitment * commitment)) : int ={
      var c;
      c <$ (duniform (range 0 3));
      return c;
  }

  proc respond (sw : (matrix * (vector *  vector *  vector) * (vector -> vector -> vector))*
    ((vector * vector * vector) * (vector * vector * vector)), ms :
    (key*commitment * commitment * commitment * commitment) *
    ((vector * vector) * matrix  *  (* m1, m2, r, dr *)
    (vector * vector * vector) * (vector4 * vector4 * vector4) * (* (r1,r2,r3),(e1_j,e2_j,e3_j) *)
    (int list * int list * int list) * (list4 * list4 * list4) * (*(pi1,pi2,pi3),(pi1_j,pi2_j,pi3_j) *)
    (vector * vector * vector) * (*  (catv u1 v1,catv u2 v2,catv u3 v3) *)
    (* (t11,t12,t13),(t21,t22,t23),(t31,t32,t33) *)
    (vector * vector * vector) *  (vector * vector * vector) *  (vector * vector * vector) * 
    opening * opening * opening * opening * (* d0 d1 d2 d3 *)
    (vector4 * vector4 * vector4) * (vector4 * vector4 * vector4) * (* (t11_j,t12_j,t13_j),(t21_j,t22_j,t23_j) *)
    (vector4 * vector4 * vector4) *
     (vector4 * vector4 * vector4 * vector4 * vector4 * vector4)),  e : int) :
   (*  (pi1,   t10,     t11,     pi1_j,  t10_j,    t11_j,       y1,    *)   
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) * matrix *
    (* d10, d11, d12, dr, dTilde0  *)opening * opening * opening   ={
      
      var m1, m2, m3, r1, r2, r3, r, pi1, pi2, pi3, pi1_j, pi2_j, pi3_j;
      var u1v1, u2v2, u3v3, y1, y2, y3, e1_j, e2_j, e3_j;
      var t10, t11, t12, t20, t21, t22, t30, t31, t32;
      var mw1, mw2, mw3, rw1, rw2, rw3;
      var t10_j, t11_j, t12_j, t20_j, t21_j, t22_j, t30_j, t31_j, t32_j;
      var d0, d1, d2, d3, resp;
      var u1_j,u2_j,u3_j,v1_j,v2_j,v3_j;

      (mw1, mw2, mw3) <- sw.`2.`1;
      (rw1, rw2, rw3) <- sw.`2.`2;
      (m1, m2) <- ms.`2.`1;
      m3 <- sw.`1.`3 m1 m2;
      r <- ms.`2.`2;
      (r1,r2,r3) <- ms.`2.`3;
      (e1_j,e2_j,e3_j) <- ms.`2.`4;
      (pi1, pi2, pi3) <- ms.`2.`5;
      (pi1_j, pi2_j, pi3_j) <- ms.`2.`6;
      (u1v1, u2v2, u3v3) <- ms.`2.`7;
      (t10,t11,t12) <- ms.`2.`8;
      (t20,t21,t22) <- ms.`2.`9;
      (t30,t31,t32) <- ms.`2.`10;
      d0 <- ms.`2.`11;
      d1 <- ms.`2.`12;
      d2 <- ms.`2.`13;
      d3 <- ms.`2.`14;
      (t10_j,t11_j,t12_j) <- ms.`2.`15;
      (t20_j,t21_j,t22_j) <- ms.`2.`16;
      (t30_j,t31_j,t32_j) <- ms.`2.`17;
      (u1_j,u2_j,u3_j,v1_j,v2_j,v3_j) <- ms.`2.`18;
      
      y1 <- JKPT12commit4 sw.`1.`1 m1 r1 e1_j;
      y2 <- JKPT12commit4 sw.`1.`1 m2 r2 e2_j;
      y3 <- JKPT12commit4 sw.`1.`1 m3 r3 e3_j;
      
                           (* pi_i, t_i0, t_i1, pij_i, tj_i0, tj_i1, R', and random coins 7 commits *)
      if (e=0) {
      resp <- ((pi1,   t10,  t11,  pi1_j, t10_j, t11_j, zerok4, u1v1, u1_j, v1_j),
               (pi2,   t20,  t21,  pi2_j, t20_j, t21_j, zerok4, u2v2, u2_j, v2_j),
               (pi3,   t30,  t31,  pi3_j, t30_j, t31_j, zerok4, u3v3, u3_j, v3_j),r,d0,d1,d2);

                       (* pi_i, t_i0, t_i2, pij_i, tj_i0, tj_i2, y, and random coins*)
      } else {if (e=1) {
      resp <-  ((pi1, t10,  t12,  pi1_j, t10_j, t12_j, y1,u1v1 + (rw1 || mw1), addv4 u1_j (subl4 r1), addv4 v1_j (subv4 m1)),
                (pi2,   t20,  t22,  pi2_j, t20_j, t22_j, y2, u2v2 + (rw2 || mw2), addv4 u2_j (subl4 r2), addv4 v2_j (subv4 m2)),
                (pi3,   t30,  t32,  pi3_j, t30_j, t32_j, y3, u3v3 + (rw3 || mw3), addv4 u3_j (subl4 r3), addv4 v3_j (subv4 m3)),
                       r,d0,d1,d3); }

            (*t_i1, t_i2, tj_i1, tj_i2, y, and random coins *)
                           else {
     resp <- (([], t11,  t12, ([],[],[],[]),  t11_j, t12_j, y1, zerov (l + v), subl4 r1, subv4 m1),
           ([], t21,  t22, ([],[],[],[]),  t21_j, t22_j, y2, zerov (l + v), subl4 r2, subv4 m2),
           ([], t31,  t32, ([],[],[],[]),  t31_j, t32_j, y3, zerov (l + v), subl4 r3, subv4 m3),
             zerom v (4*v), d2, d2, d3);}}

     return resp;
  }

  
  proc verify (x: matrix * (vector *  vector *  vector) * (vector -> vector -> vector),
      m: (key*commitment * commitment * commitment * commitment), e:int ,
      z: (*  (pi1,   t10,     t11,     pi1_j,  t10_j,    t11_j,       y1,    *)   
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) * matrix *
    (* d10, d11, d12, dr, dTilde0  *)opening * opening * opening ) : bool ={
      var a, key, respComm, respOther;
      var c0, c1, c2, c3;
      var pi1, pi2, pi3, pi1_j, pi2_j, pi3_j, y1, y2, y3, y1_j, y2_j, y3_j, r;
      var t10, t11, t20, t21, t30, t31, t10_j, t11_j,  t20_j, t21_j, t30_j, t31_j;
      var d0, d1, d2, u1v1, u2v2, u3v3, u1_j, u2_j, u3_j, v1_j, v2_j, v3_j;

    respComm <- false;
    respOther <- false;
    a <- x.`1;
    key <- m.`1;
    (y1, y2, y3)              <- x.`2; 
    c0                        <- m.`2;
    c1                        <- m.`3;
    c2                        <- m.`4;
    c3                        <- m.`5;
    (pi1,   t10,  t11,  pi1_j, t10_j, t11_j, y1_j, u1v1, u1_j, v1_j) <- z.`1;
    (pi2,   t20,  t21,  pi2_j, t20_j, t21_j, y2_j, u2v2, u2_j, v2_j) <- z.`2;
    (pi3,   t30,  t31,  pi3_j, t30_j, t31_j, y3_j, u3v3, u3_j, v3_j) <- z.`3;
    (r,d0,d1,d2) <- (z.`4, z.`5, z.`6, z.`7);
  
    if (e=0) { (* P opens C_i0, C_i1, Cj_i0, Cj_i1, C_R *)
      respComm <-  verify key (permToVector pi1, permToVector pi2, permToVector pi3, t0_perm4 pi1_j,
        t0_perm4 pi2_j, t0_perm4 pi3_j, zerov4) (c0, d0) /\
        verify key (t10, t20, t30, t10_j, t20_j,t30_j,(matrixToVector r, zerov 0, zerov 0, zerov 0)) (c1, d1) /\
        verify key (t11, t21, t31, t11_j, t21_j, t31_j, zerov4) (c2, d2);
      (* π0i, π0ji ∈ Sk(ai, bi) *)
      respOther <- isPerm pi1 /\ isPerm pi2 /\ isPerm pi3 /\ isPerm4 pi1_j /\ isPerm4 pi2_j /\ isPerm4 pi3_j /\
      (* t_i0 ⊕ π_0−1i (ti1) = A.(ai || bi) *)
      a *^ u1v1   = (t10 + permVector t11  (invPerm pi1)) /\ a *^ u2v2   = (t20 + permVector t21  (invPerm pi2)) /\
      a *^ u3v3   = (t30 + permVector t31  (invPerm pi3)) /\ (e0_check a u1_j v1_j t10_j t11_j pi1_j) /\
      (e0_check a u2_j v2_j t20_j t21_j pi2_j) /\ (e0_check a u3_j v3_j t30_j t31_j pi3_j) /\
      (*  which satisfy bi =P4j=1 R0j.bji. *)
      (subv u1v1 l (l+v)) = v_calc r v1_j /\ (subv u2v2 l (l+v)) = v_calc r v2_j /\ (subv u3v3 l (l+v)) = v_calc r v3_j;
    }
    
    else { if (e=1) { (* P opens C_i0, C_i2, Cj_i0, Cj_i2, C, tildeC, C_R *)
        respComm <- verify key (permToVector pi1, permToVector pi2, permToVector pi3, t0_perm4 pi1_j,
           t0_perm4 pi2_j, t0_perm4 pi3_j, zerov4) (c0, d0) /\
        verify key (t10, t20, t30, t10_j, t20_j, t30_j, (matrixToVector r, zerov 0, zerov 0, zerov 0)) (c1, d1) /\
        verify key (t11, t21, t31, t11_j, t21_j, t31_j, (compact y1_j, compact y2_j, compact y3_j, zerov 0)) (c3, d2);
        (* π0i, π0ji ∈ Sk(ai, bi) *)
        respOther <- isPerm pi1 /\ isPerm pi2 /\ isPerm pi3 /\ isPerm4 pi1_j /\ isPerm4 pi2_j /\ isPerm4 pi3_j /\
        (* s (ai, bi),(aji, bji) ∈ I` × Ivto the equations ti0 ⊕π0−1i(ti2)⊕yi = A.(aikbi) *)
        a *^ u1v1   = (t10 + permVector t11  (invPerm pi1) + y1) /\ a *^ u2v2   = (t20 + permVector t21  (invPerm pi2) + y2) /\
        a *^ u3v3   = (t30 + permVector t31  (invPerm pi3) + y3) /\ (e1_check a u1_j v1_j t10_j t11_j y1_j pi1_j) /\
        (e1_check a u2_j v2_j t20_j t21_j y2_j pi2_j) /\ (e1_check a u3_j v3_j t30_j t31_j y3_j pi3_j) /\
          (* satisfy  bi =P4j=1 R0j.bji.*)
        (subv u1v1 l (l+v)) = v_calc r v1_j /\ (subv u2v2 l (l+v)) = v_calc r v2_j /\ (subv u3v3 l (l+v)) = v_calc r v3_j /\
        validMatrix r;
      }
    
      else { if (e=2) { (* P opens C_i1, C_i2, Cj_i1, Cj_i2, C˜ *)
        respComm <- verify key (t10, t20, t30, t10_j, t20_j, t30_j, zerov4) (c2, d1) /\
        verify key (t11,t21,t31,t11_j,t21_j,t31_j, (compact y1_j, compact y2_j, compact y3_j, zerov 0)) (c3, d2); 
        (* kti1 ⊕ ti2k1 = ktji1 ⊕ tji2k1?= w  *)
        respOther <-checkW (t10-t11) /\ checkW (t20-t21) /\ checkW (t30-t31) /\ checkW4 t10_j t11_j /\
        checkW4 t20_j t21_j /\ checkW4 t30_j t31_j /\ checkWComm a y1_j u1_j v1_j /\ checkWComm a y2_j u2_j v2_j /\
        checkWComm a y3_j u3_j v3_j /\
        v3_j = subv4 (x.`3 (compact v1_j) (compact v2_j));
        }}}
    
    return respComm /\ respOther /\ l + v = cols a /\ size y1 = k /\ size y2 = k /\
      size y3 = k /\ size u1v1 = l + v /\ size u2v2 = l + v /\ size u3v3 = l + v /\
      size t10 = k /\ size t20 = k /\ size t30 = k /\ size t11 = k /\
      size t21 = k /\ size t31 = k /\ rows a = k /\ (forall w z, size (x.`3 w z) = 4 * v)
      /\ size r = (v, 4 * v) /\ size_v4 v1_j /\ size_v4 v2_j /\ size_v4 v3_j /\ size_k4 y1_j /\ size_k4 y2_j /\ size_k4 y3_j /\
      size_k4 t10_j /\ size_k4 t20_j /\ size_k4 t30_j /\  size_k4 t11_j /\ size_k4 t21_j /\ size_k4 t31_j /\
      size_l4 u1_j /\ size_l4 u2_j /\ size_l4 u3_j /\ validFunction x.`3 /\
     (forall (x1 y1 x2 y2 : vector), x.`3 (x1 + x2) (y1 + y2) = (x.`3 x1 y1) + (x.`3 x2 y2));
  } 
}.

module MultiRelAlg : SigmaAlgorithms ={
  proc soundness (h:  matrix * (vector *  vector *  vector) * (vector -> vector -> vector),
  m : (key*commitment * commitment * commitment * commitment),
  z  : (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) * matrix *
    opening * opening * opening,
   z' :  (int list * vector * vector * list4 * vector4 * vector4 * vector4 *  vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) * matrix *
    opening * opening * opening,
   z'':  (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) * matrix *
    opening * opening * opening) :
   ((vector*vector*vector)*(vector*vector*vector)) option ={
    var rCatM0, rCatM1, rCatM2;
    rCatM0 <- z'.`1.`8 - z.`1.`8;
    rCatM1 <- z'.`2.`8 - z.`2.`8;
    rCatM2 <- z'.`3.`8 - z.`3.`8;
      return Some ((subv rCatM0 l (l+v), subv rCatM1 l (l+v), subv rCatM2 l (l+v)),
                   (subv rCatM0 0 l,subv rCatM1 0 l,subv rCatM2 0 l));
  }

  proc simulate (h:  matrix * (vector *  vector *  vector) * (vector->vector->vector),  e: int) :
    (key*commitment * commitment * commitment * commitment)*
  ((int list * vector * vector * list4 * vector4 * vector4 * vector4 *  vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) *
   (int list * vector * vector * list4 * vector4 * vector4 * vector4 * vector * vector4 * vector4) * matrix *
    opening * opening * opening) = {
   
      var key, pi1,pi2,pi3,v1,v2,v3,u1,u2,u3,f1,f2,f3,b, f1_j, f2_j, f3_j, r, resp; 
      
      var t10, t11, t12, t20, t21, t22, t30, t31, t32;
      var t10_j, t11_j, t12_j, t20_j, t21_j, t22_j, t30_j, t31_j, t32_j;
      var u1_j, u2_j, u3_j, v1_j, v2_j, v3_j,  pi1_j, pi2_j, pi3_j;
      var e1_j, e2_j, e3_j, m1, m2, m3, r1, r2, r3, y1, y2, y3;
      var c0, c1, c2, c3, d0, d1, d2, d3;
      var u1v1, u2v2, u3v3, rr0, rr1, rr2, rr3;

      key <$ keygen;
      
      (* Sample the vectors *)
      m1 <$ dvector dR (4*v);
      m2 <$ dvector dR (4*v);
      (* and computer v3 *)
      m3 <- h.`3 m1 m2;
   
      v1_j <$ dRv4;
      v2_j <$ dRv4;
      v3_j <$ dRv4;

      r <$ R_sample2 v1_j v2_j v3_j m1 m2 m3;
    
      v1 <- v_calc r v1_j;
      v2 <- v_calc r v2_j;
      v3 <- v_calc r v3_j;
         
      (* other vector info *)
      r1 <$ dvector dR (4*l);
      r2 <$ dvector dR (4*l);
      r3 <$ dvector dR (4*l);

      (* compute the vectors to commit to *)
      e1_j <$ dW4;
      e2_j <$ dW4;
      e3_j <$ dW4;
 
      y1 <- JKPT12commit4 h.`1 m1 r1 e1_j;
      y2 <- JKPT12commit4 h.`1 m2 r2 e2_j;
      y3 <- JKPT12commit4 h.`1 m3 r3 e3_j;


      pi1 <$ (duniform (allperms (range 0 k)));
      pi2 <$ (duniform (allperms (range 0 k)));
      pi3 <$ (duniform (allperms (range 0 k)));
      pi1_j <$ perm4;
      pi2_j <$ perm4;
      pi3_j <$ perm4;

      u1_j <$ dRl4;
      u2_j <$ dRl4;
      u3_j <$ dRl4;

      u1 <$ dvector dR l;
      u2 <$ dvector dR l;
      u3 <$dvector dR l;
   
      f1 <$ dvector dR k;
      f2 <$ dvector dR k;
      f3 <$ dvector dR k;
      f1_j <$ dRk4;
      f2_j <$ dRk4;
      f3_j <$ dRk4;  

      b <$ chi;

      if (e =1){
        t10 <-  h.`1 *^ (catv u1 v1) + f1 + h.`2.`1;
        t20 <-  h.`1 *^ (catv u2 v2) + f2 + h.`2.`2;
        t30 <-  h.`1 *^ (catv u3 v3) + f3 + h.`2.`3;
      } else {
      t10 <-  h.`1 *^ (catv u1 v1) + f1;
      t20 <-  h.`1 *^ (catv u2 v2) + f2;
      t30 <-  h.`1 *^ (catv u3 v3) + f3;
      }
      
      t11 <- permVector (- f1) pi1;
      t21 <- permVector (- f2) pi2;
      t31 <- permVector (- f3) pi3;
      
      t12 <-  permVector (-f1 + b) pi1;
      t22 <-  permVector (-f2 + b) pi2;
      t32 <-  permVector (-f3 + b) pi3;

      if (e =1){
        t10_j <- t0_4 h.`1 u1_j (addv4 v1_j (subv4 m1)) f1_j;
        t20_j <- t0_4 h.`1 u2_j (addv4 v2_j (subv4 m2)) f2_j;
        t30_j <- t0_4 h.`1 u3_j (addv4 v3_j (subv4 m3)) f3_j;
      } else {
        t10_j <- t0_4 h.`1 u1_j v1_j f1_j;
        t20_j <- t0_4 h.`1 u2_j v2_j f2_j;
        t30_j <- t0_4 h.`1 u3_j v3_j f3_j;
      }
   
      t11_j <- t1_4 f1_j pi1_j;
      t12_j <- t2_4 f1_j e1_j pi1_j;
    
      t21_j <- t1_4 f2_j pi2_j;
      t22_j <- t2_4 f2_j e2_j pi2_j;
   
      t31_j <- t1_4 f3_j pi3_j;
      t32_j <- t2_4 f3_j e3_j pi3_j;

      rr0 <$ commit_rand;
      rr1 <$ commit_rand;
      rr2 <$ commit_rand;
      rr3 <$ commit_rand;

      (c0, d0) <- commit key (permToVector pi1,permToVector pi2, permToVector pi3,
        t0_perm4 pi1_j, t0_perm4 pi2_j, t0_perm4 pi3_j, zerov4) rr0;

      (c1, d1) <- commit key (t10, t20, t30,  t10_j, t20_j, t30_j, (matrixToVector r, zerov 0, zerov 0, zerov 0)) rr1;

      (c2, d2) <- commit key (t11, t21, t31, t11_j, t21_j, t31_j, zerov4) rr2;

      (c3, d3) <- commit key (t12, t22, t32, t12_j, t22_j, t32_j,  (compact y1, compact y2, compact y3, zerov 0)) rr3;

      if (e=0) {
        (c3, d3) <- commit key (zerov (l+v),zerov (l+v),zerov (l+v), zerov4, zerov4, zerov4, zerov4) rr3;
      }
      if (e=1) {
        (c2,d2) <- commit key (zerov (l+v),zerov (l+v),zerov (l+v), zerov4, zerov4, zerov4, zerov4) rr2;
        (c3,d3) <- commit key (t11, t21, t31, t12_j, t22_j, t32_j, (compact y1, compact y2, compact y3, zerov 0)) rr3;
      }
      if (e=2) {
        (c0,d0) <- commit key (zerov (l+v),zerov (l+v),zerov (l+v), zerov4, zerov4, zerov4, zerov4) rr0;
        (c1,d1) <- commit key (zerov (l+v),zerov (l+v),zerov (l+v), zerov4, zerov4, zerov4, zerov4) rr1;
      }

      (u1v1, u2v2, u3v3) <- (catv u1 v1,catv u2 v2,catv u3 v3);

     if (e=0) { resp <- ((key,c0,c1,c2,c3),
        ((pi1,   t10,  t11,  pi1_j, t10_j, t11_j, zerok4, u1v1, u1_j, v1_j),
                             (pi2,   t20,  t21,  pi2_j, t20_j, t21_j, zerok4, u2v2, u2_j, v2_j),
                             (pi3,   t30,  t31,  pi3_j, t30_j, t31_j, zerok4, u3v3, u3_j, v3_j),r,d0,d1,d2));

                       (* pi_i, t_i0, t_i2, pij_i, tj_i0, tj_i2, R',y, and random coins*)
      } else { if (e=1) { resp <- ((key,c0,c1,c2,c3),
      ((pi1,   t10,  t11,  pi1_j, t10_j, t12_j, y1, u1v1, addv4 u1_j (subl4 r1), v1_j),
      (pi2,   t20,  t21,  pi2_j, t20_j, t22_j, y2, u2v2, addv4 u2_j (subl4 r2), v2_j),
      (pi3,   t30,  t31,  pi3_j, t30_j, t32_j, y3, u3v3, addv4 u3_j (subl4 r3), v3_j),r,d0,d1,d3));

            (*t_i1, t_i2, tj_i1, tj_i2, y, and random coins *)
      } else { resp <- ((key,c0,c1,c2,c3),
                       (([], t11,  t12, ([],[],[],[]),  t11_j, t12_j, y1, zerov (l + v), subl4 r1, subv4 m1),
           ([], t21,  t22, ([],[],[],[]),  t21_j, t22_j, y2, zerov (l + v), subl4 r2, subv4 m2),
           ([], t31,  t32, ([],[],[],[]),  t31_j, t32_j, y3, zerov (l + v), subl4 r3, subv4 m3),zerom v (4*v), d2, d2, d3)); }}

    return resp;
  }
}.

section Security.




local lemma c0_simp c0 : c0 \in duniform (range 0 3) => c0 <> 0 => c0 <> 1 => c0 =2.
    smt(@Distr @List).
  qed.

local lemma e_0_simple m (u v : vector) f pi :
  pi \in duniform (allperms (range 0 k)) =>
  f \in dvector dR k =>
  rows m = k =>
  m *^ (u || v) =
  m *^ (u || v) + f +
  permVector (permVector (-f) pi) (invPerm pi).
proof.
  move => h0 h1 h2. have : isPerm pi. smt(@Distr @List @Perms). move => g0. have : size f = k.
  smt(@Distr @MLWE.M gt0_k). move => g1. rewrite permVectorInv. smt(@Distr @List @Perms). smt(@List @Distr @MLWE.M @Int).
  rewrite -addvA. rewrite addvN. rewrite lin_addv0. smt(@MLWE.M). smt(@MLWE.M).
qed.

local lemma e_0_simple_j m u v f pi:
  pi \in perm4 =>
  f \in dRk4 =>
  rows m = k =>
  e0_check m u v (t0_4 m u v f) (t1_4 f pi) pi.
proof.
  move => h0 h1 h2 @/t0_4 @/t1_4. apply samplePerm4_def in h0. apply dRk4_size in h1.
  apply e0_check_def; simplify. do! split.
  apply e_0_simple; trivial. smt(@Distr @Perms @List). smt(@Distr dR_ll dR_funi @MLWE.M).
  apply e_0_simple; trivial. smt(@Distr @Perms @List).  smt(@Distr dR_ll dR_funi @MLWE.M).
  apply e_0_simple; trivial. smt(@Distr @Perms @List).  smt(@Distr dR_ll dR_funi @MLWE.M).
  apply e_0_simple; trivial. smt(@Distr @Perms @List).  smt(@Distr dR_ll dR_funi @MLWE.M).
qed.

 (* We also use this lemma for the linear relation check *)
 local lemma e_1_simple_sub m (u v : vector) f (c w1 w2 : vector) :
   f \in dvector dR k =>
   rows m = k =>
   size c = k =>
   m *^ (u || v) + f - (f + (c - m *^ (w2 || w1))) + c = m*^ ((u || v) + (w2 || w1)).
  proof.
    move => ? ? ?. rewrite mulmxvDr. rewrite -addvA. rewrite -addvA. congr.  rewrite oppvD.
    rewrite oppvD. rewrite !addvA.  rewrite addvN. rewrite lin_add0v. smt(@MLWE.M). rewrite oppvK.
    rewrite addvC. rewrite addvA. rewrite addvN. smt(@MLWE.M).
  qed.

 local lemma e_1_simple m (u v : vector) f pi (c w2 w1 : vector) :
  pi \in duniform (allperms (range 0 k)) =>
  f \in dvector dR k =>
  rows m = k =>
  size c = k =>
   m *^ ((u || v) + (w2 || w1)) = m *^ (u || v) + f +
   permVector (permVector (- (f + (c - m *^ (w2 || w1)))) pi) (invPerm pi) +c .
proof.
  move => h0 h1 h2 h3. have : isPerm pi. smt(@Distr @List @Perms). move => g0. have : size f = k.
  smt(@Distr @MLWE.M gt0_k). move => g1.
  rewrite permVectorInv. smt(@Distr @List @Perms). smt(@List @Distr @MLWE.M @Int).
  rewrite e_1_simple_sub; trivial.
qed.

local lemma e_1_simple_j_sub a (u v f e m r : vector):
  size f = size e =>
  size e = rows a =>
  a *^ (u || v) + a *^ (r || m) =
  a *^ (u || v) + f - (f + e) + (a *^ (r || m) + e).
proof.
  move => h0 h1. rewrite -!addvA. congr. rewrite oppvD.  rewrite !addvA.  rewrite addvN. rewrite lin_add0v.
  smt(@MLWE.M). rewrite addvC.  rewrite !addvA.  rewrite addvN. rewrite lin_add0v.  smt(@MLWE.M). trivial.
qed.

local lemma e_1_simple_j a u_j v_j f_j e_j pi_j m r:
  pi_j \in perm4 =>
  f_j \in dRk4 =>
  e_j \in dW4 =>
  u_j\in dRl4 =>
  rows a = k =>
  e1_check a (addv4 u_j (subl4 r)) (addv4 v_j (subv4 m)) (t0_4 a u_j v_j f_j)
    (t2_4 f_j e_j pi_j) (JKPT12commit4 a m r e_j) pi_j.
proof.
  move => h0 h1 h2 h3 h4 @/t0_4 @/t2_4 @/JKPT12commit4 @/subl4 @/subv4 @/addv4. apply samplePerm4_def in h0.
  apply dW4size in h2. apply dRk4_size in h1. apply dRl4_size in h3.
  apply e1_check_def; simplify. do! split.
  rewrite permVectorInv. smt(). rewrite isPerm_size_k. smt(). smt(@MLWE.M). rewrite -e_1_simple_j_sub; trivial. smt(). smt().
  rewrite -addv_catv. smt(@MLWE.M). apply mulmxvDr.
  rewrite permVectorInv. smt(). rewrite isPerm_size_k. smt(). smt(@MLWE.M). rewrite -e_1_simple_j_sub; trivial. smt(). smt().
  rewrite -addv_catv. smt(@MLWE.M). apply mulmxvDr.
  rewrite permVectorInv. smt(). rewrite isPerm_size_k. smt(). smt(@MLWE.M). rewrite -e_1_simple_j_sub; trivial. smt(). smt().
  rewrite -addv_catv. smt(@MLWE.M). apply mulmxvDr.
  rewrite permVectorInv. smt(@M). rewrite isPerm_size_k. smt(). smt(@MLWE.M). rewrite -e_1_simple_j_sub; trivial. smt(). smt().
  rewrite -addv_catv. smt(@MLWE.M). apply mulmxvDr.
qed.

local lemma size_l u : u  \in dvector dR l => l = size u.
    proof.
      smt(@MLWE.M gt0_l).
  qed.

    local lemma checkWHelp (f e :  vector) pi :  pi \in duniform (allperms (range 0 k)) => size f = k =>
     size e = k => checkW e =>
     checkW (permVector (-f) pi - permVector (- (f + e)) pi).
  proof.
    move => h0 h1 h2 h3. have : isPerm pi. smt(@Distr @Perms @List). move => h5.
    rewrite permVectorOp; trivial. rewrite permVectorAdd; trivial. smt(@MLWE.M @List). rewrite size_oppv.
    rewrite size_oppv. smt(@MLWE.M @List). rewrite -checkWPerm. trivial.  rewrite oppvK. rewrite addvA. rewrite (addvC _ f).
    rewrite addvN. rewrite addvC. rewrite lin_addv0. smt(@MLWE.M). trivial. rewrite oppvK. rewrite addvA. rewrite (addvC _ f).
    rewrite addvN. rewrite addvC. rewrite lin_addv0. smt(@MLWE.M).  smt(@MLWE.M).
  qed.

local lemma checkWHelp2 f_j pi_j e_j :
  pi_j \in perm4 =>
  e_j \in dW4 =>
  f_j \in dRk4 =>
  checkW4 (t1_4 f_j pi_j) (t2_4 f_j e_j pi_j).
proof.
  move => h0 h1 h2 @/t1_4 @/t2_4. have : e_j \in dW4. trivial. move => h3. apply dW4_def in h1. apply samplePerm4_def in h0.
  apply dRk4_size in h2. apply dW4size in h3. simplify. do! split; simplify.
  apply checkWHelp. apply isPermSimp2.  smt(). smt(). smt(). smt(chi_weight).
  apply checkWHelp. apply isPermSimp2.  smt(). smt(). smt(). smt(chi_weight).
  apply checkWHelp. apply isPermSimp2.  smt(). smt(). smt(). smt(chi_weight).
  apply checkWHelp. apply isPermSimp2.  smt(). smt(). smt(). smt(chi_weight).
qed.

local lemma checkWHelp2_1 f_j pi_j e_j :
  pi_j \in perm4 =>
  e_j \in dW4 =>
  f_j \in dRk4 =>
  checkW ((t1_4 f_j pi_j).`1 - (t2_4 f_j e_j pi_j).`1).
proof.
  smt(checkWHelp2).
qed.

local lemma checkWHelp2_2 f_j pi_j e_j :
  pi_j \in perm4 =>
  e_j \in dW4 =>
  f_j \in dRk4 =>
  checkW ((t1_4 f_j pi_j).`2 - (t2_4 f_j e_j pi_j).`2).
proof.
  smt(checkWHelp2).
qed.


local lemma checkWHelp2_3 f_j pi_j e_j :
  pi_j \in perm4 =>
  e_j \in dW4 =>
  f_j \in dRk4 =>
  checkW ((t1_4 f_j pi_j).`3 - (t2_4 f_j e_j pi_j).`3).
proof.
  smt(checkWHelp2).
qed.

local lemma checkWHelp2_4 f_j pi_j e_j :
  pi_j \in perm4 =>
  e_j \in dW4 =>
  f_j \in dRk4 =>
  checkW ((t1_4 f_j pi_j).`4 - (t2_4 f_j e_j pi_j).`4).
proof.
  smt(checkWHelp2).
qed.



local lemma inImageSound A (t u w u' w' : vector) pi (c : vector) :
      isPerm pi =>
      size u' = k =>
      size w' = k =>
      size t = k =>
      size c = k =>
      A *^ u = (t + permVector u' (invPerm pi)) =>
      A *^ w = (t + permVector w' (invPerm pi) + c) =>
      checkW (u' - w') =>
      checkW (c - A *^ (u - w)).
  proof.
    move => h1 h2 h3 h4 h5 h6 h7 h8. rewrite mulmxvDr. rewrite (bRing w). rewrite h6. rewrite h7.
    have : (t + permVector u' (invPerm pi) + (t + permVector w' (invPerm pi) + c)) = (c + permVector ((-u') + w') (invPerm pi)).
    have : forall (a b c d : vector), a + b = d => a + (b + c) = c + d.  smt(@MLWE.M). move => h'. apply h'.
    rewrite (addvC _ (permVector w' (invPerm pi))). rewrite -addvA. rewrite (addvA _ _ t). rewrite permVectorAdd.
    apply invPermPerm. apply h1. rewrite isPerm_size_k. apply invPermPerm; trivial. smt().
    rewrite isPerm_size_k. apply invPermPerm; trivial. smt().
    pose q := (permVector (u' + w') (invPerm pi) + t). rewrite -(bRing t). move => @/q. rewrite addvC. rewrite -addvA.
    rewrite addvN. rewrite lin_addv0. rewrite permVectorSize. apply invPermPerm; trivial. smt(). smt(bRing).  move => h'.
    rewrite h'. rewrite oppvD. rewrite addvA. rewrite addvN. rewrite lin_add0v.  rewrite !bRing. rewrite permVectorSize.
    apply invPermPerm; trivial. smt(). rewrite bRing. rewrite -checkWPerm. apply invPermPerm; trivial.
    rewrite bRing. rewrite -(bRing w'). trivial. smt(@M). smt(bRing).
  qed.

local lemma sound_open A (c u w u' w' t : vector) pi :
      isPerm pi =>
      l + v = cols A =>
      size c = k =>
      size u = l + v =>
      size w = l + v =>
      size u' = k =>
      size w' = k =>
      size t = k =>
      A *^ u = (t + permVector u' (invPerm pi)) =>
      A *^ w = (t + permVector w' (invPerm pi) + c) =>
      checkW (u' - w') =>
      checkW (c - A *^ (subv (w - u) 0 l || subv (w - u) l (l + v))).
  proof.
    move => h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11. rewrite catv_subvC_gen. smt(@MLWE.M). smt(@MLWE.M gt0_l gt0_v). 
    (* Showing that image actutally exists *)
    rewrite (addvC w). rewrite (bRing u). rewrite -(bRing w). apply (inImageSound _ t _ _ u' w' pi _); trivial.
  qed. 


lemma MulitRelProt_Sound (F <: SigmaFaker)  &m:
  hoare[SpecialSoundnessExperiment(MultiRelProt, MultiRelAlg, F).main : true ==> res].
proof.
  proc. inline *. auto. call(_:true). auto. move => _ [[A [y1 y2 y3] f] [k  c0 c1 c2 c3]].
    move => [[e0pi1 e0t10 e0t11 e0pi1_j e0t10_j e0t11_j e0y1 e0u1v1 e0u1_j e0v1_j]
             [e0pi2 e0t20 e0t21 e0pi2_j e0t20_j e0t21_j e0y2 e0u2v2 e0u2_j e0v2_j]
             [e0pi3 e0t30 e0t31 e0pi3_j e0t30_j e0t31_j e0y3 e0u3v3 e0u3_j e0v3_j] e0r e0d0 e0d1 e0d2].
          
    move => [[e1pi1 e1t10 e1t11 e1pi1_j e1t10_j e1t11_j e1y1 e1u1v1 e1u1_j e1v1_j]
            [e1pi2 e1t20 e1t21 e1pi2_j e1t20_j e1t21_j e1y2 e1u2v2 e1u2_j e1v2_j]
            [e1pi3 e1t30 e1t31 e1pi3_j e1t30_j e1t31_j e1y3 e1u3v3 e1u3_j e1v3_j] e1r e1d0 e1d1 e1d2].
          
    move => [[e2pi1 e2t10 e2t11 e2pi1_j e2t10_j e2t11_j e2y1 e2u1v1 e2u1_j e2v1_j]
            [e2pi2 e2t20 e2t21 e2pi2_j e2t20_j e2t21_j e2y2 e2u2v2 e2u2_j e2v2_j]
            [e2pi3 e2t30 e2t31 e2pi3_j e2t30_j e2t31_j e2y3 e2u3v3 e2u3_j e2v3_j] e2r e2d0 e2d1 e2d2].

   simplify. move => h. elim h => h0 h. elim h => h1 h2.
   (* Using commitments and clear - c0 *)
   have : (permToVector e0pi1, permToVector e0pi2, permToVector e0pi3,
            t0_perm4 e0pi1_j, t0_perm4 e0pi2_j, t0_perm4 e0pi3_j, zerov4) =
          (permToVector e1pi1, permToVector e1pi2, permToVector e1pi3,
            t0_perm4 e1pi1_j, t0_perm4 e1pi2_j, t0_perm4 e1pi3_j, zerov4). apply (commit_verify_sound k  _ _ c0 e0d0 e1d0).
   smt(). smt(). move => h. have : (e0pi1, e0pi2, e0pi3) = (e1pi1, e1pi2, e1pi3). smt(permToVectorInj).
   move => h'. elim h' => ->> ->> ->>. have : (e0pi1_j, e0pi2_j, e0pi3_j) = (e1pi1_j, e1pi2_j, e1pi3_j). smt(permToVectorInj).
   move => h'. elim h' => ->> ->> ->>.  clear h. elim h0 => h0 h00. elim h1 => h1 h11. elim h0 => h0 h000. elim h1 => h1 h111.
   clear h0 h1 c0 e0d0 e1d0.
   (* c1 *)
   have : (e0t10, e0t20, e0t30, e0t10_j, e0t20_j, e0t30_j,(matrixToVector e0r, zerov 0, zerov 0, zerov 0)) = 
          (e1t10, e1t20, e1t30, e1t10_j, e1t20_j, e1t30_j, (matrixToVector e1r, zerov 0, zerov 0, zerov 0)).
    apply (commit_verify_sound k  _ _ c1 e0d1 e1d1). smt(). smt(). move => h'. elim h' => ->> ->> ->> ->> ->> ->>. move => h'.
   have : e0r = e1r. smt(matrixToVectorInj). move => ->>. elim h000 => h0 h000. elim h111 => h1 h111. clear h' h0 h1 c1 e0d1 e1d1.
   (* c2 *)
   have :  (e0t11, e0t21, e0t31, e0t11_j, e0t21_j, e0t31_j, zerov4) = (e2t10, e2t20, e2t30, e2t10_j, e2t20_j, e2t30_j, zerov4).
   apply (commit_verify_sound k  _ _ c2 e0d2 e2d1). smt(). smt(). move => h'. elim h' => ->> ->> ->> ->> ->> ->> _.
   elim h2 => h2 h22. elim h2 => h2 h222. clear c2 h2 h000 e0d2 e2d1.
   (* c3 *)
   have : (e1t11, e1t21, e1t31, e1t11_j, e1t21_j, e1t31_j, (compact e1y1, compact e1y2, compact e1y3, zerov 0)) =       
          (e2t11, e2t21, e2t31, e2t11_j, e2t21_j, e2t31_j, (compact e2y1, compact e2y2, compact e2y3, zerov 0)).
   apply (commit_verify_sound k  _ _ c3 e1d2 e2d2). smt(). smt(). move => h'. elim h' => ->> ->> ->> ->> ->> ->> h.
            have : (e1y1, e1y2, e1y3) = (e2y1, e2y2, e2y3). smt(compact_bij_k). move => h'. elim h' => ->> ->> ->>.
   clear h h111 h222 c3 e1d2 e2d2.
          
    (* general clean *)
    elim h00 => h h00. elim h => h000 h. clear h000. elim h => h000 h. clear h000. elim h => h000 h. clear h000.
    elim h => h000 h. clear h000. elim h => h000 h. clear h000. elim h => h000 h. clear h000. 
          
    (* start main *)      
    progress; simplify. apply (sound_open _ _ _ _ e2t10 e2t11 e1t10 e1pi1); trivial. smt(). smt(). smt(). smt(). smt(). 
    smt(). smt(). smt(). smt(). smt(). smt().
    apply (sound_open _ _ _ _ e2t20 e2t21 e1t20 e1pi2); trivial. smt(). smt(). smt(). smt(). smt(). 
              smt(). smt(). smt(). smt(). smt(). smt().
    apply (sound_open _ _ _ _ e2t30 e2t31 e1t30 e1pi3); trivial. smt(). smt(). smt(). smt(). smt(). 
              smt(). smt(). smt(). smt(). smt(). smt().

    (* Need to prove the relation holds*)
    (* Lets start by showing we have valid openings to y_j *)
    have : checkWComm A e2y1 (e1u1_j - e0u1_j) (e1v1_j - e0v1_j).
    apply (e_check_simp2 _ _ _ _ _ e1t10_j e2t11_j e2t10_j _ e1pi1_j); smt().
    have : checkWComm A e2y2 (e1u2_j - e0u2_j) (e1v2_j - e0v2_j).
    apply (e_check_simp2 _ _ _ _ _ e1t20_j e2t21_j e2t20_j _ e1pi2_j); smt().
    have : checkWComm A e2y3 (e1u3_j - e0u3_j) (e1v3_j - e0v3_j).
    apply (e_check_simp2 _ _ _ _ _ e1t30_j e2t31_j e2t30_j _ e1pi3_j); smt(). move => h_y1_j h_y2_j h_y3_j.     

    (* m'_i = R' m~'_i *)
    rewrite subv_addv. smt(@MLWE.M). elim h11 => h10 h100. elim h10 => h3 h10. elim h10 => h4 h10. elim h10 => h5 h10.
    elim h10 => h6 h10. elim h10 => h7 h10. elim h10 => h8 h10. elim h10 => h9 h10. elim h10 => h01 h10. elim h10 => h02 h10.
    elim h10 => h03 h10. elim h10 => h04 h10. elim h10 => h05 h10. elim h10 => h06 h10. elim h10 => h07 h08. rewrite bRing.
    rewrite h08. rewrite subv_addv. smt(@MLWE.M). rewrite subv_addv. smt(@MLWE.M). rewrite h07. rewrite h06.
    elim h => h11 h. elim h => h12 h. elim h => h13 h. elim h => h14 h. elim h => h15 h. elim h => h16 h.
    elim h => h17 h. elim h => h18 h19. rewrite bRing. rewrite bRing. rewrite h17. rewrite h18. rewrite h19. 
    rewrite v_calc_mat. smt(). smt(). rewrite v_calc_mat. smt(). smt().
    rewrite v_calc_mat. smt(). smt(). rewrite v_calc_mat. smt(). smt(). 
    rewrite v_calc_mat. smt(). smt(). rewrite v_calc_mat. smt(). smt().
    rewrite -!mulmxvDr. rewrite -(bRing (compact e0v3_j)). rewrite -(bRing (compact e0v1_j)). rewrite -(bRing (compact e0v2_j)).
  
    (* Use the sounds of JKTP12 commitments and matrix property *)
    have : e1v3_j - e0v3_j = e2v3_j. apply (JKPT12_sound4 A e2y3 (e1u3_j - e0u3_j) _ e2u3_j). smt(). smt().
    have : e1v2_j - e0v2_j = e2v2_j. apply (JKPT12_sound4 A e2y2 (e1u2_j - e0u2_j) _ e2u2_j). smt(). smt().
    have : e1v1_j - e0v1_j = e2v1_j. apply (JKPT12_sound4 A e2y1 (e1u1_j - e0u1_j) _ e2u1_j). smt(). smt().
    move => g0 g1 g2. rewrite validMatrix_validFunction. smt(). smt(). rewrite compact_neg_v. smt(). smt(). 
    rewrite compact_neg_v. smt(). smt(). rewrite compact_neg_v. smt(). smt(). rewrite g0. rewrite g1. rewrite g2. 
    elim h22 => h h21. rewrite h. rewrite compact_subv4. smt(). trivial.

    (* size constraint *)
    smt(). smt(). smt(). smt(). smt(). smt(gt0_l). smt(gt0_l gt0_v). smt(gt0_l). smt(gt0_l gt0_v). smt(gt0_l).
    smt(gt0_l gt0_v). smt(). smt(). smt().
  qed.
        
local lemma dvector_size x k : 0 < k => x \in dvector dR k => size x = k.
    move => h h'. smt(@Distr @MLWE.M).
  qed.
  
local lemma t1_simp A (u v' f r m c: vector):
    u \in dvector dR l => l + v = cols A => rows A = k => f \in dvector dR k => size r = l =>
    size c = k =>
     A *^ (u || v') + f =
     A *^ (u +r || v' + m) + (f - (c - A *^ (r || m))) + c.
  proof.
     move => h0 h1 h2 h3 h4 h5. rewrite -addv_catv. smt(@MLWE.M). rewrite mulmxvDr. rewrite -!addvA.
     congr. rewrite (addvC (A *^ _)). rewrite !bRing. rewrite addvA. rewrite -addvA.
     apply bRing_cancel_sub. smt(size_mulmxv @MLWE.M). trivial.
  qed.

lemma neg_simp_l (a b : vector) : size a = l => size b = l =>  a = a + b + b.
    move => h0 h1. pose q := a + b. rewrite -(bRing b). move => @/q. rewrite -addvA. rewrite addvN.
    rewrite lin_addv0. smt(). trivial.
qed.

lemma neg_simp_k (a b : vector) : size a = k => size b = k =>  a = a + b + b.
    move => h0 h1. pose q := a + b. rewrite -(bRing b). move => @/q. rewrite -addvA. rewrite addvN.
    rewrite lin_addv0. smt(). trivial.   
qed.

lemma neg_simp_v (a b : vector) : size a = v => size b = v =>  a = a + b + b.
    move => h0 h1. pose q := a + b. rewrite -(bRing b). move => @/q. rewrite -addvA. rewrite addvN.
    rewrite lin_addv0. smt(). trivial.
qed.

lemma dRin2 (a b : vector)  k : 0 < k => size a = k => size b = k => a - b \in dvector dR k.
    move => h0 h1 h2. apply dRin. smt(@MLWE.M).
qed.

lemma neg_simp_v4 v1 (m1 : vector) : size_v4 v1 => size m1 = 4 * v => v1 = addv4 (addv4 v1 (subv4 m1)) (subv4 m1). 
proof.
   move => [g0 [g1 [g2 g3]]] h1 @/addv4 @/subv4. simplify. rewrite -neg_simp_v; trivial.
  smt(@MLWE.M). rewrite -neg_simp_v; trivial. smt(@MLWE.M). rewrite -neg_simp_v; trivial. smt(@MLWE.M).
  rewrite -neg_simp_v; trivial. smt(@MLWE.M). smt().
qed.
  
lemma leq_lt l : 0 < l => 0 <= l.
    smt().
  qed.

local lemma t2_simp (f b v : vector) (pi : int list)  :
    f \in dvector dR k  =>
    b \in chi =>
    size v = k =>  
    pi \in duniform (allperms (range 0 k)) =>
    checkW v  =>  
    permVector (f + v) pi =
    permVector ((permVector f (invPerm  (findPermEq v b)) +  b)) (composePerm (findPermEq v b) pi).
  proof.
  move => h0 h1 h2 h3 h5. have : size pi = k. apply isPerm_size_k. apply isPermSimp. trivial.
  move => h4. rewrite -composePermCorrect. rewrite size_addv. rewrite permVectorSize. apply invPermPerm. apply findPermChecks.
  smt(chi_k). apply findPermChecks. apply isPermSimp. trivial. rewrite -permVectorAdd. apply isPermSimp. trivial. smt(@M).
  smt(@M). rewrite -permVectorAdd. apply findPermChecks. rewrite permVectorSize. apply invPermPerm. apply findPermChecks.
  apply findPermSize. smt(findPermSize chi_k). rewrite composePermCorrect. smt(@M). apply invPermPerm. apply findPermChecks.
    apply findPermChecks. rewrite composePermNeg. apply findPermChecks. rewrite permVectorID. smt(@M).
    rewrite -findPermCorr. apply permEqWeight; trivial. smt(). smt(chi_k). rewrite h5. smt(chi_weight). apply permVectorAdd.
  apply isPermSimp; trivial. smt(@M). smt(@M).
qed.

  local lemma l_max l : l = max l l.
    proof.
    smt().
  qed.


   (* The reduction from the ZK adversary to the commitment scheme adversary *)
  module U (D : Decider) : Unhider = {
    var ck : key
    var m1, m2, m3, r1, r2, r3, u1, u2, u3, f1, f2, f3, bW: vector
    var v1_j, v2_j, v3_j, e1_j, e2_j, e3_j, y1, y2, y3, u1_j, u2_j, u3_j, f1_j, f2_j, f3_j : vector4
    var r : matrix
    var pi1, pi2, pi3 : int list
    var pi1_j, pi2_j, pi3_j : list4
    
    proc choose(x:key,a:(matrix * (vector *  vector *  vector) * (vector -> vector -> vector))*
    ((vector * vector * vector) *(vector*vector*vector))*int) = {
      var v1, v2, v3, e1, e2, e3, t11, t12, t13, t21, t22, t23, t31, t32, t33;
      var t11_j, t12_j, t13_j, t21_j, t22_j, t23_j, t31_j, t32_j, t33_j;
      
      (* Sample the vectors *)
      m1 <$ dvector dR (4*v);
      m2 <$ dvector dR (4*v);
      (* and computer v3 *)
      m3 <- a.`1.`3 m1 m2;
      
      v1_j <$ dRv4;
      v2_j <$ dRv4;
      v3_j <$ dRv4;
      
      r <$ R_sample a.`2.`1.`1 a.`2.`1.`2 a.`2.`1.`3 m1 m2 m3;

      v1 <- v_calc r v1_j;
      v2 <- v_calc r v2_j;
      v3 <- v_calc r v3_j;

      (* other vector info *)
      r1 <$ dvector dR (4*l);
      r2 <$ dvector dR (4*l);
      r3 <$ dvector dR (4*l);

      (* compute the vectors to commit to *)
      e1_j <$ dW4;
      e2_j <$ dW4;
      e3_j <$ dW4;
      y1 <- JKPT12commit4 a.`1.`1 m1 r1 e1_j;
      y2 <- JKPT12commit4 a.`1.`1 m2 r2 e2_j;
      y3 <- JKPT12commit4 a.`1.`1 m3 r3 e3_j;

      (* Sample the permutations *)
      pi1 <$ (duniform (allperms (range 0 k)));
      pi2 <$ (duniform (allperms (range 0 k)));
      pi3 <$ (duniform (allperms (range 0 k)));
      pi1_j <$ perm4;
      pi2_j <$ perm4;
      pi3_j <$ perm4;

      (* sample more vector *)
      u1_j <$ dRl4;
      u2_j <$ dRl4;
      u3_j <$ dRl4;
    
      u1 <$ dvector dR l;
      u2 <$ dvector dR l;
      u3 <$ dvector dR l;

      e1 <- a.`1.`2.`1 - (a.`1.`1 *^ (catv a.`2.`2.`1 a.`2.`1.`1));
      e2 <- a.`1.`2.`2 - (a.`1.`1 *^ (catv a.`2.`2.`2 a.`2.`1.`2));
      e3 <- a.`1.`2.`3 - (a.`1.`1 *^ (catv a.`2.`2.`3 a.`2.`1.`3));
    
      f1 <$ dvector dR k;
      f2 <$ dvector dR k;
      f3 <$ dvector dR k;
      f1_j <$ dRk4;
      f2_j <$ dRk4;
      f3_j <$ dRk4;  

      bW <$ chi;
    
      t11 <-  a.`1.`1 *^ (catv u1 v1) + f1;
      t12 <- permVector (- f1) pi1;
      t13 <-  permVector (-(f1 + e1)) pi1;
    
      t21 <-  a.`1.`1 *^ (catv u2 v2) + f2;
      t22 <- permVector (- f2) pi2;
      t23 <-  permVector (-(f2 + e2)) pi2;
    
      t31 <-  a.`1.`1 *^ (catv u3 v3) + f3;
      t32 <- permVector (- f3) pi3;
      t33 <-  permVector (-(f3 + e3)) pi3;

      t11_j <- t0_4 a.`1.`1 u1_j v1_j f1_j;
      t12_j <- t1_4 f1_j pi1_j;
      t13_j <- t2_4 f1_j e1_j pi1_j;
    
      t21_j <- t0_4 a.`1.`1 u2_j v2_j f2_j;
      t22_j <- t1_4 f2_j pi2_j;
      t23_j <- t2_4 f2_j e2_j pi2_j;
    
      t31_j <- t0_4 a.`1.`1 u3_j v3_j f3_j;
      t32_j <- t1_4 f3_j pi3_j;
      t33_j <- t2_4 f3_j e3_j pi3_j;

      ck <- x;

      return (((zerov (l+v), zerov (l+v), zerov (l+v),zerov4,zerov4,zerov4,zerov4),
        (zerov (l+v), zerov (l+v), zerov (l+v),zerov4,zerov4,zerov4,zerov4)),
      
        (if (a.`3 = 2) then
          (permToVector (composePerm (invPerm (findPermEq e1 bW)) pi1),
           permToVector (composePerm (invPerm (findPermEq e2 bW)) pi2),
            permToVector (composePerm (invPerm (findPermEq e3 bW)) pi3), t0_perm4 pi1_j, t0_perm4 pi2_j, t0_perm4 pi3_j, zerov4) else
          (t13,t23,t33,t13_j,t23_j,t33_j, (compact y1, compact y2, compact y3, zerov 0)),
          
        if (a.`3 = 1) then  (permVector (-f1 + (a.`1.`2.`1 - a.`1.`1 *^ (a.`2.`2.`1 || a.`2.`1.`1))) pi1,
            permVector (-f2 + (a.`1.`2.`2 - a.`1.`1 *^ (a.`2.`2.`2 || a.`2.`1.`2))) pi2,
            permVector (-f3 + (a.`1.`2.`3 - a.`1.`1 *^ (a.`2.`2.`3 || a.`2.`1.`3))) pi3, t12_j, t22_j, t32_j, zerov4)
        else (a.`1.`1 *^ (catv u1 v1) + (permVector f1  (findPermEq e1 bW)),
              a.`1.`1 *^ (catv u2 v2) + (permVector f2  (findPermEq e2 bW)),
            a.`1.`1 *^ (catv u3 v3) + (permVector f3  (findPermEq e3 bW)), t11_j, t21_j, t31_j,
          
           (matrixToVector r, zerov 0, zerov 0, zerov 0))));
    }

    proc guess(c:commitment*commitment,a:(matrix * (vector*vector*vector) * (vector->vector->vector))*
    ((vector * vector * vector) *(vector*vector*vector))*int) = {
      var c0,c1,c2,c3,d0,d1,d2,d3, cr1, cr2, cr3, cr4, b, com, resp;
      var v1, v2, v3;
      var t11, t12, t13, t21, t22, t23, t31, t32, t33, e1, e2, e3, u1v1, u2v2, u3v3;
      var t11_j, t12_j, t13_j, t21_j, t22_j, t23_j, t31_j, t32_j, t33_j;

      v1 <- v_calc r v1_j;
      v2 <- v_calc r v2_j;
      v3 <- v_calc r v3_j;

       e1 <- a.`1.`2.`1 - (a.`1.`1 *^ (catv a.`2.`2.`1 a.`2.`1.`1));
      e2 <- a.`1.`2.`2 - (a.`1.`1 *^ (catv a.`2.`2.`2 a.`2.`1.`2));
      e3 <- a.`1.`2.`3 - (a.`1.`1 *^ (catv a.`2.`2.`3 a.`2.`1.`3));
        
      if (a.`3 =1){
        t11 <-  a.`1.`1 *^ (catv u1 v1) + f1 + a.`1.`2.`1;
        t21 <-  a.`1.`1 *^ (catv u2 v2) + f2 + a.`1.`2.`2;
        t31 <-  a.`1.`1 *^ (catv u3 v3) + f3 + a.`1.`2.`3;
      } else {
        t11 <-  a.`1.`1 *^ (catv u1 v1) + f1;
        t21 <-  a.`1.`1 *^ (catv u2 v2) + f2;
        t31 <-  a.`1.`1 *^ (catv u3 v3) + f3;
      }
      
      t12 <- permVector (- f1) pi1;
      t13 <-  permVector (-(f1 + e1)) pi1;
      
      t22 <- permVector (- f2) pi2;
      t23 <-  permVector (-(f2 + e2)) pi2;
    
      t32 <- permVector (- f3) pi3;
      t33 <-  permVector (-(f3 + e3)) pi3;

      if (a.`3 =1){
        t11_j <- t0_4 a.`1.`1 u1_j (addv4 v1_j (subv4 m1)) f1_j;
        t21_j <- t0_4 a.`1.`1 u2_j (addv4 v2_j (subv4 m2)) f2_j;
        t31_j <- t0_4 a.`1.`1 u3_j (addv4 v3_j (subv4 m3)) f3_j;
      } else {
        t11_j <- t0_4 a.`1.`1 u1_j v1_j f1_j;
        t21_j <- t0_4 a.`1.`1 u2_j v2_j f2_j;
        t31_j <- t0_4 a.`1.`1 u3_j v3_j f3_j;
      }
      

      t12_j <- t1_4 f1_j pi1_j;  
      t13_j <- t2_4 f1_j e1_j pi1_j;
    
      t22_j <- t1_4 f2_j pi2_j;
      t23_j <- t2_4 f2_j e2_j pi2_j;
    
      t32_j <- t1_4 f3_j pi3_j;
      t33_j <- t2_4 f3_j e3_j pi3_j;

      u1v1 <- catv u1 v1;
      u2v2 <- catv u2 v2; 
      u3v3 <- catv u3 v3;

      cr1 <$ commit_rand;
      cr2 <$ commit_rand;
      cr3 <$ commit_rand;
      cr4 <$ commit_rand;

       (c0, d0) <- commit ck (permToVector pi1,permToVector pi2, permToVector pi3,
        t0_perm4 pi1_j, t0_perm4 pi2_j, t0_perm4 pi3_j, zerov4) cr1;

      (c1, d1) <- commit ck (t11, t21, t31,  t11_j, t21_j, t31_j, (matrixToVector r, zerov 0, zerov 0, zerov 0)) cr2;

      (c2, d2) <- commit ck (t12, t22, t32, t12_j, t22_j, t32_j, zerov4) cr3;

      (c3, d3) <- commit ck (t13, t23, t33, t13_j, t23_j, t33_j,  (compact y1, compact y2, compact y3, zerov 0)) cr4;
      
      if (a.`3=1) {
        (c3,d3) <- commit ck (t12, t22, t32, t13_j, t23_j, t33_j, (compact y1, compact y2, compact y3, zerov 0)) cr4;
      } else {
        (c3,d3) <- commit ck (permVector (f1 + bW) pi1, permVector (f2 + bW) pi2, permVector (f3 + bW) pi3, t13_j, t23_j, t33_j,  (compact y1, compact y2, compact y3, zerov 0)) cr4; }
    
      
        com <- if (a.`3 = 0) then (ck,c0,c1,c2,c.`1) else (
        if (a.`3 = 1) then (ck,c0,c1,c.`2,c3) else
          (ck,c.`1,c.`2,c2,c3));

        
      if (a.`3=0) {
      resp <- ((pi1,   t11,  t12,  pi1_j, t11_j, t12_j, zerok4, u1v1, u1_j, v1_j),
               (pi2,   t21,  t22,  pi2_j, t21_j, t22_j, zerok4,  u2v2, u2_j, v2_j),
               (pi3,   t31,  t32,  pi3_j, t31_j, t32_j, zerok4, u3v3, u3_j, v3_j),r,d0,d1,d2);

                       (* pi_i, t_i0, t_i2, pij_i, tj_i0, tj_i2, y, and random coins*)
                          } else {if (a.`3=1) {
      resp <-  ((pi1,  t11,  t12,  pi1_j, t11_j, t13_j, y1, u1v1, addv4 u1_j (subl4 r1), v1_j),
               (pi2,   t21,  t22,  pi2_j, t21_j, t23_j, y2, u2v2, addv4 u2_j (subl4 r2), v2_j),
               (pi3,   t31,  t32,  pi3_j, t31_j, t33_j, y3, u3v3, addv4 u3_j (subl4 r3), v3_j),
                       r,d0,d1,d3); }

            (*t_i1, t_i2, tj_i1, tj_i2, y, and random coins *)
                           else {
           resp <- (([], t12,  permVector (-(f1+ bW)) pi1, ([],[],[],[]),  t12_j, t13_j,
                 y1, zerov (l + v), subl4 r1, subv4 m1),
               ([], t22, permVector (-(f2+ bW)) pi2, ([],[],[],[]),  t22_j, t23_j,
                 y2, zerov (l + v), subl4 r2, subv4 m2),
               ([], t32,  permVector (-(f3+ bW)) pi3, ([],[],[],[]),  t32_j, t33_j,
                 y3, zerov (l + v), subl4 r3, subv4 m3),
             zerom v (4*v), d2, d2, d3);}}  
      
      b <@ D.distinguish(a.`1, com,a.`3,resp);
      return b;
    }
  }.

  declare module D <: Decider {-U.ck, -U.m1, -U.m2, -U.m3, -U.r1, -U.r2, -U.r3, -U.u1, -U.u2, -U.u3,
    -U.f1, -U.f2, -U.f3, -U.bW, -U.v1_j, -U.v2_j, -U.v3_j, -U.e1_j, -U.e2_j, -U.e3_j, -U.y1, -U.y2, -U.y3,
    -U.u1_j, -U.u2_j, -U.u3_j, -U.f1_j, -U.f2_j, -U.f3_j, -U.r, -U.pi1, -U.pi2, -U.pi3, -U.pi1_j, -U.pi2_j,
    -U.pi3_j}.

  local lemma Real_GB_0 s w e &m :
        e \in range 0 3 =>
      Pr[SHVZK(MultiRelProt, MultiRelAlg, D).simulate(s,e) @ &m : res] =
        Pr[HidingExperimentL(U(D)).main((s,w,e)) @ &m : res].
  proof.     
    move => Ran.
  case(e = 0) => he1. subst. byequiv. proc. inline *. rcondt{2} 104. auto. progress. rcondf{2} 84. auto. progress.
    rcondt{1} 68. auto. progress. wp. call(_:true). wp.
    swap{2} [96..99] -31. wp. rnd{2}. rnd. rnd{2}.
    auto. progress. apply R_sample_equiv.
    apply (R_sample_equiv2 v1_jL v2_jL v3_jL w.`1.`1 w.`1.`2 w.`1.`3 m1L m2L (h{1}.`3 m1L m2L)). trivial.
    apply commit_rand_ll. auto. auto.
    (* challenge case 1 *)
  case(e = 1) => he2. subst. byequiv. proc. inline *. rcondf{2} 104. auto. progress. rcondt{2} 104. auto. progress.
    rcondf{1} 68. auto. progress. rcondt{1} 68. auto. progress. wp. call(_:true). wp.
    swap{2} [94..97] -29. wp. swap{2} 70 - 3. rnd{2}.
    rnd. rnd{2}.  auto. progress. apply R_sample_equiv.
    apply (R_sample_equiv2 v1_jL v2_jL v3_jL w.`1.`1 w.`1.`2 w.`1.`3 m1L m2L (h{1}.`3 m1L m2L)). trivial.
    apply commit_rand_ll. auto. auto.
    (* challenge case 2 *)
    have : (e =2). smt(@List). move => he3. subst. byequiv. proc. inline *. rcondf{1} 42. auto. progress.
    rcondf{1} 51. auto. progress. rcondf{1} 68. auto. progress.  rcondf{1} 68. auto. progress. rcondt{1} 68. auto. progress.
    rcondf{1} 71. auto. progress. rcondf{1} 71. auto. progress.  rcondf{2} 84. auto. progress.
    rcondf{2} 106. auto. progress. rcondf{2} 106. auto. progress. wp. call(_:true). wp. 
    swap{2} [96..99] -29. wp. rnd. rnd. rnd{2}. rnd{2}. auto. progress. apply R_sample_equiv.
    apply (R_sample_equiv2 v1_jL v2_jL v3_jL w.`1.`1 w.`1.`2 w.`1.`3 m1L m2L (h{1}.`3 m1L m2L)).
    smt(). apply commit_rand_ll. rewrite !bRing. trivial.
    rewrite !bRing. trivial. rewrite !bRing. trivial. rewrite !bRing. trivial.
    rewrite !bRing. trivial. auto. auto. 
  qed.

  local lemma gt0_4v : 0 < 4 * v. smt(gt0_v). qed. 
  
  local lemma Real_GB_1 s w e &m :
        R s w =>
        e \in range 0 3 =>
        Pr[SHVZK(MultiRelProt, MultiRelAlg, D).real(s,w,e) @ &m : res] =
        Pr[HidingExperimentR(U(D)).main((s,w,e)) @ &m : res].
        proof.
          move => @/R Rel Ran.
  elim: Rel => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
  (* case 0 *)
  case (e = 0). move => he. rewrite he.  byequiv => //. proc. inline *. wp. call(_:true). rcondt{2} 104. auto. progress.
  rcondt{1} 98. auto. progress. wp. swap{2} [94..97] -29. wp. rnd{2}. rnd. rnd{2}. rnd. rnd. rnd. wp. rnd{2}.
          auto. progress. apply chi_ll. apply commit_rand_ll.

  (* case 1 *)
  case (e =1). move => he h0. rewrite he. byequiv => //. proc. inline *. rcondt{2} 77. auto. progress.
  rcondt{2} 86. auto. progress. rcondf{1} 098. auto. progress. rcondt{1} 98. auto. progress. rcondf{2} 108. auto. progress.
  rcondt{2} 108. auto. progress. wp. call(_:true). wp.
  swap{2} [98..101] -33. wp. swap{2} 70 -3. rnd{2}. rnd. rnd{2}. rnd. rnd. rnd. wp. rnd{2}. rnd. rnd. rnd.
  (* sample f *)  rnd(fun (f : vector), f - (h{1}.`2.`3 - h{1}.`1 *^ (w{2}.`2.`3 || w{2}.`1.`3)))
   (fun (f : vector), f + (h{1}.`2.`3 - h{1}.`1 *^ (w{2}.`2.`3 || w{2}.`1.`3))).
   rnd(fun (f : vector), f - (h{1}.`2.`2 - h{1}.`1 *^ (w{2}.`2.`2 || w{2}.`1.`2)))
     (fun (f : vector), f + (h{1}.`2.`2 - h{1}.`1 *^ (w{2}.`2.`2 || w{2}.`1.`2))).
   rnd(fun (f : vector), f - (h{1}.`2.`1 - h{1}.`1 *^ (w{2}.`2.`1 || w{2}.`1.`1)))
     (fun (f : vector), f + (h{1}.`2.`1 - h{1}.`1 *^ (w{2}.`2.`1 || w{2}.`1.`1))). wp.
  (* sample u (s) *)
     rnd(fun b, b - w{2}.`2.`3)(fun b, b +  w{2}.`2.`3).
     rnd(fun b, b - w{2}.`2.`2)(fun b, b +  w{2}.`2.`2).
       rnd(fun b, b - w{2}.`2.`1)(fun b, b +  w{2}.`2.`1).
  (* jump forward *)
       rnd. rnd. rnd. rnd. rnd. rnd. rnd. rnd. rnd. wp. rnd. rnd. rnd. rnd. rnd. rnd. wp. rnd.
       rnd (fun v, addv4 v (subv4 m3{1}))(fun v, addv4 v (subv4 m3{1})).
       rnd (fun v, addv4 v (subv4 m2{1}))(fun v, addv4 v (subv4 m2{1})).
       rnd (fun v, addv4 v (subv4 m1{1}))(fun v, addv4 v (subv4 m1{1})). wp. rnd. rnd. wp.  
        
  (* sampling correct - I way want to simplify this. *)
       (* v *) auto. progress.
    apply neg_simp_v4. apply dRv4_v4. trivial. apply dvector_size. apply gt0_4v. trivial.
  apply dRmu1_v4. apply dRv4_v4. trivial. apply subv4_v4. apply dRin_v4. apply size_addv4. apply dRv4_v4. trivial. apply subv4_v4.
  apply neg_simp_v4. apply dRv4_v4. trivial. apply dvector_size. apply gt0_4v. trivial.
   apply neg_simp_v4. apply dRv4_v4. trivial. apply dvector_size. apply gt0_4v. trivial.
  apply dRmu1_v4. apply dRv4_v4. trivial. apply subv4_v4. apply dRin_v4. apply size_addv4. apply dRv4_v4. trivial. apply subv4_v4.
       apply neg_simp_v4. apply dRv4_v4. trivial. apply dvector_size. apply gt0_4v. trivial.
       apply neg_simp_v4. apply dRv4_v4. trivial. apply g15.
   apply dRmu1_v4. apply dRv4_v4. trivial. apply subv4_v4.   
   apply dRin_v4. apply size_addv4. apply dRv4_v4. trivial. apply subv4_v4.  
   apply neg_simp_v4. apply dRv4_v4. trivial. apply g15.
  (* u *) rewrite bRing. apply neg_simp_l. apply dvector_size. apply gt0_l. trivial. apply g9. apply dRmu1ss.
  apply dvector_size. apply gt0_l. trivial. apply g9. apply dRin2. apply gt0_l. apply dvector_size. apply gt0_l. trivial. apply g9.
  rewrite bRing. apply neg_simp_l.  apply dvector_size. apply gt0_l. trivial. apply g9.
  rewrite bRing. apply neg_simp_l. apply dvector_size. apply gt0_l. trivial. apply g11. apply dRmu1ss.
       apply dvector_size. apply gt0_l. trivial. apply g11. apply dRin2. apply gt0_l. apply dvector_size. apply gt0_l. trivial.
       apply g11. rewrite bRing. apply neg_simp_l.  apply dvector_size. apply gt0_l. trivial. apply g11.
  rewrite bRing. apply neg_simp_l. apply dvector_size. apply gt0_l. trivial. apply g13. apply dRmu1ss. apply dvector_size.
  apply gt0_l. trivial. apply g13. apply dRin2. apply gt0_l. apply dvector_size. apply gt0_l. trivial. apply g13.
  rewrite bRing. apply neg_simp_l.  apply dvector_size. apply gt0_l. trivial. apply g13.
  (* f *) rewrite !bRing. apply neg_simp_k.  apply dvector_size. apply gt0_k. trivial. rewrite size_addv. rewrite g4.
  rewrite size_mulmxv. apply g7.
  apply dRmu1ss. apply dvector_size. apply gt0_k. trivial.  rewrite size_addv. rewrite g4.
  rewrite bRing. rewrite size_mulmxv. apply g7.
   apply dRin2. apply gt0_k. apply dvector_size. apply gt0_k. trivial. rewrite bRing.  rewrite size_addv. rewrite g4.
  rewrite size_mulmxv. apply g7.
  rewrite !bRing. apply neg_simp_k. apply dvector_size. apply gt0_k. trivial.  rewrite size_addv. rewrite g4.
  rewrite size_mulmxv. apply g7.
  rewrite !bRing. apply neg_simp_k.  apply dvector_size. apply gt0_k. trivial.  rewrite size_addv. rewrite g5.
  rewrite size_mulmxv. apply g7.
  apply dRmu1ss. apply dvector_size. apply gt0_k. trivial. rewrite size_addv. rewrite g5. rewrite bRing.
  rewrite size_mulmxv. apply g7.
   apply dRin2. apply gt0_k. apply dvector_size. apply gt0_k. trivial. rewrite size_addv. rewrite g5. rewrite bRing.
  rewrite size_mulmxv. apply g7.
  rewrite bRing. apply neg_simp_k. apply dvector_size. apply gt0_k. trivial. rewrite size_addv. rewrite g5. rewrite bRing.
  rewrite size_mulmxv. apply g7.
  rewrite !bRing. apply neg_simp_k.  apply dvector_size. apply gt0_k. trivial. rewrite size_addv. rewrite g6. 
  rewrite size_mulmxv. apply g7.
  apply dRmu1ss. apply dvector_size. apply gt0_k. trivial.  rewrite size_addv. rewrite g6. rewrite bRing.
  rewrite size_mulmxv. apply g7.
  apply dRin2. apply gt0_k. apply dvector_size. apply gt0_k. trivial. rewrite size_addv.
  rewrite g6. rewrite bRing. rewrite size_mulmxv. apply g7.
   rewrite !bRing. apply neg_simp_k. apply dvector_size. apply gt0_k. trivial.  rewrite size_addv. rewrite g6. 
  rewrite size_mulmxv. apply g7.
  (* last bit *) apply chi_ll. apply commit_rand_ll.

  (* c1 - com *) rewrite !v_calc_addv4. congr. congr. congr.
  rewrite (v_calc_swap_1 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)).
       trivial. apply dvector_size. apply gt0_4v. trivial. rewrite bRing. apply t1_simp; trivial. smt().
  rewrite (v_calc_swap_2 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)).
       trivial. apply dvector_size. apply gt0_4v. trivial. rewrite bRing. apply t1_simp; trivial. smt().
  rewrite (v_calc_swap_3 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)).
       trivial. apply g15. rewrite bRing. apply t1_simp; trivial. smt().
  rewrite -neg_simp_v4. apply dRv4_v4. trivial. apply dvector_size. trivial. apply gt0_4v. trivial. trivial.
 rewrite -neg_simp_v4. apply dRv4_v4. trivial. apply dvector_size. trivial. apply gt0_4v. trivial. trivial.
       rewrite -neg_simp_v4. apply dRv4_v4. trivial. apply g15. trivial.

  (* c2 *)  congr. congr. congr. rewrite !bRing. rewrite -bRing_cancel. rewrite size_addv.
  smt(@MLWE.M). trivial.
  rewrite !bRing. rewrite -bRing_cancel. rewrite size_addv. smt(@MLWE.M). trivial.
  rewrite !bRing. rewrite -bRing_cancel. rewrite size_addv. smt(@MLWE.M). trivial.

  (* c3 *) congr. congr. congr. rewrite !bRing. trivial. rewrite !bRing. trivial.
  rewrite !bRing. trivial. 
     
  (* t's *)  rewrite !v_calc_addv4. rewrite (v_calc_swap_1 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)).
   trivial. apply dvector_size. apply gt0_4v. trivial. rewrite bRing. apply t1_simp; trivial. smt().
   rewrite !bRing. trivial. rewrite -neg_simp_v4. apply dRv4_v4. trivial. apply dvector_size. trivial.
   apply gt0_4v. trivial. trivial. rewrite v_calc_addv4. rewrite (v_calc_swap_1 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)). trivial. smt(@MLWE.M). rewrite bRing. rewrite addv_catv.
       rewrite g9. apply dvector_size. apply gt0_l. trivial. trivial.
  rewrite v_calc_addv4. rewrite (v_calc_swap_2 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)). trivial. smt(@MLWE.M). rewrite bRing. apply t1_simp; trivial. smt().
  rewrite !bRing. trivial. rewrite -neg_simp_v4. apply dRv4_v4. trivial.
  apply dvector_size. trivial. apply gt0_4v. trivial. trivial. rewrite addv_catv. rewrite g11.
       apply dvector_size. apply gt0_l. trivial. rewrite v_calc_addv4.
       rewrite (v_calc_swap_2 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)). trivial. apply dvector_size.
       apply gt0_4v. trivial. rewrite bRing. trivial. rewrite !v_calc_addv4.
       rewrite (v_calc_swap_3 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)); trivial. apply g15.
       rewrite bRing. apply t1_simp; trivial. smt(). rewrite !bRing. trivial. 
       rewrite -neg_simp_v4. apply dRv4_v4. trivial. apply g15. trivial.
       rewrite v_calc_addv4. rewrite (v_calc_swap_3 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)). trivial. apply g15.
       rewrite !bRing. apply addv_catv. rewrite g13.  apply dvector_size. apply gt0_l. trivial.

  (* c1 - opening *)  rewrite !v_calc_addv4. congr. congr. congr.
  rewrite (v_calc_swap_1 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)).
       trivial. apply dvector_size. apply gt0_4v. trivial. rewrite bRing. apply t1_simp; trivial. smt().
  rewrite (v_calc_swap_2 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)).
       trivial. apply dvector_size. apply gt0_4v. trivial. rewrite bRing. apply t1_simp; trivial. smt().
  rewrite (v_calc_swap_3 w{1}.`1.`1 w{1}.`1.`2 w{1}.`1.`3 m1L m2L (h{1}.`3 m1L m2L)).
       trivial. apply g15. rewrite bRing. apply t1_simp; trivial. smt().
  rewrite -neg_simp_v4. apply dRv4_v4. trivial. apply dvector_size. trivial. apply gt0_4v. trivial. trivial.
 rewrite -neg_simp_v4. apply dRv4_v4. trivial. apply dvector_size. trivial. apply gt0_4v. trivial. trivial.
       rewrite -neg_simp_v4. apply dRv4_v4. trivial. apply g15. trivial.

  (* c3 - opeing *) rewrite !bRing. congr.

  (* case e = 2 *)
  move => h1 h2. have : e = 2. smt(@List). move => he. rewrite he.
  byequiv => //. proc. inline *. wp. call(_:true). rcondf{2} 77. auto. progress.
  rcondf{2} 86. auto. progress. rcondf{1} 98. auto. progress. rcondf{1} 98. auto. progress.
  rcondf{2} 106. auto. progress. rcondf{2} 108. auto. progress. rcondf{2} 108. auto. progress.
  wp. swap{2} [98..101] -31. wp. rnd. rnd. rnd{2}. rnd{2}. rnd. rnd. wp. swap{2} 44 -40. rnd. rnd. rnd.
  (* Sample f *) rnd(fun (f : vector),
     permVector (f) (invPerm (findPermEq (- (h{1}.`2.`3 - h{1}.`1 *^ (w{2}.`2.`3 || w{2}.`1.`3))) U.bW{2})))
     (fun (f:vector), permVector (f) (findPermEq (- (h{1}.`2.`3 - h{1}.`1 *^ (w{2}.`2.`3 || w{2}.`1.`3))) U.bW{2})).
     rnd (fun (f : vector), permVector (f) (invPerm (findPermEq  (- (h{1}.`2.`2 - h{1}.`1 *^ (w{2}.`2.`2 || w{2}.`1.`2))) U.bW{2} )))
     (fun (f:vector), permVector (f) (findPermEq (- (h{1}.`2.`2 - h{1}.`1 *^ (w{2}.`2.`2 || w{2}.`1.`2))) U.bW{2})).
      rnd (fun (f : vector), permVector (f) (invPerm (findPermEq (- (h{1}.`2.`1 - h{1}.`1 *^ (w{2}.`2.`1 || w{2}.`1.`1)))  U.bW{2})))
     (fun (f:vector), permVector (f) (findPermEq (- (h{1}.`2.`1 - h{1}.`1 *^ (w{2}.`2.`1 || w{2}.`1.`1))) U.bW{2})). wp.
       rnd. rnd. rnd. rnd. rnd. rnd. rnd. rnd. rnd.
  (* Sample pi *) rnd(fun pi, composePerm 
       (findPermEq (-(h{1}.`2.`3 - h{1}.`1 *^ (w{1}.`2.`3 || w{1}.`1.`3))) (U.bW{2}) ) pi{2})
     (fun pi, (composePerm (invPerm
           (findPermEq (-(h{1}.`2.`3 - h{1}.`1 *^ (w{1}.`2.`3 || w{1}.`1.`3))) (U.bW{2})))  pi{2} )).
      rnd(fun pi, composePerm
       (findPermEq (-(h{1}.`2.`2 - h{1}.`1 *^ (w{1}.`2.`2 || w{1}.`1.`2)))  (U.bW{2}) )  pi{2})
     (fun pi, (composePerm (invPerm
           (findPermEq (-(h{1}.`2.`2 - h{1}.`1 *^ (w{1}.`2.`2 || w{1}.`1.`2)))  (U.bW{2})))  pi{2})).
      rnd(fun pi, composePerm
       (findPermEq (-(h{1}.`2.`1 - h{1}.`1 *^ (w{1}.`2.`1 || w{1}.`1.`1)))  (U.bW{2}) )  pi{2})
     (fun pi, (composePerm (invPerm
           (findPermEq (-(h{1}.`2.`1 - h{1}.`1 *^ (w{1}.`2.`1 || w{1}.`1.`1)))  (U.bW{2})))  pi{2})).
             auto. rnd{2}. auto. progress. apply chi_ll.

   (* sampling correct *)
   rewrite -composePermA. apply findPermChecks. apply invPermPerm. apply findPermChecks. apply isPermSimp; trivial.
   rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial. trivial.
   apply mu1Perm. apply isPermSimp. trivial. apply composePermPerm. apply invPermPerm. apply findPermChecks. 
   apply isPermSimp. trivial. apply isPermSimp2. apply composePermPerm. apply findPermChecks. apply isPermSimp. trivial.
   rewrite -composePermA. apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial.
             rewrite composePermNeg. apply findPermChecks. rewrite composePermID. trivial. apply isPermSimp; trivial. trivial.
   rewrite -composePermA. apply findPermChecks. apply invPermPerm. apply findPermChecks. apply isPermSimp; trivial.
   rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial. trivial.
   apply mu1Perm. apply isPermSimp. trivial. apply composePermPerm. apply invPermPerm. apply findPermChecks. 
   apply isPermSimp. trivial. apply isPermSimp2. apply composePermPerm. apply findPermChecks. apply isPermSimp. trivial.
   rewrite -composePermA. apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial.
             rewrite composePermNeg. apply findPermChecks. rewrite composePermID. trivial. apply isPermSimp; trivial. trivial.
   rewrite -composePermA. apply findPermChecks. apply invPermPerm. apply findPermChecks. apply isPermSimp; trivial.
   rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial. trivial.
   apply mu1Perm. apply isPermSimp. trivial. apply composePermPerm. apply invPermPerm. apply findPermChecks. 
   apply isPermSimp. trivial. apply isPermSimp2. apply composePermPerm. apply findPermChecks. apply isPermSimp. trivial.
   rewrite -composePermA. apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial.
   rewrite composePermNeg. apply findPermChecks. rewrite composePermID. trivial. apply isPermSimp; trivial. trivial.
 
   (* samling f *) rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial. apply findPermChecks. apply invPermPerm.
   apply findPermChecks. rewrite composePermNeg. apply findPermChecks. rewrite permVectorID. apply dvector_size. apply gt0_k.
   trivial.  trivial. apply dRpermPres. apply findPermChecks. rewrite eq_sym. apply dvector_size. apply gt0_k. trivial.
   apply dRpermPres2. trivial. apply invPermPerm. apply findPermChecks.  rewrite composePermCorrect.
   apply dvector_size. apply gt0_k. trivial. apply invPermPerm. apply findPermChecks. apply findPermChecks. rewrite composePermNeg.
   apply findPermChecks. rewrite permVectorID. apply dvector_size. apply gt0_k. trivial. trivial.
   rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply findPermChecks. apply invPermPerm.
   apply findPermChecks. rewrite composePermNeg. apply findPermChecks. rewrite permVectorID.
   apply dvector_size. apply gt0_k. trivial. trivial. apply dRpermPres. apply findPermChecks. rewrite eq_sym.
   apply dvector_size. apply gt0_k. trivial. apply dRpermPres2. trivial.
             apply invPermPerm. apply findPermChecks.  rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.
             apply invPermPerm. apply findPermChecks. apply findPermChecks. rewrite composePermNeg. apply findPermChecks.
             rewrite permVectorID. apply dvector_size. apply gt0_k. trivial. trivial.
   rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply findPermChecks. apply invPermPerm.
             apply findPermChecks. rewrite composePermNeg. apply findPermChecks. rewrite permVectorID.
   apply dvector_size. apply gt0_k. trivial. trivial.
   apply dRpermPres. apply findPermChecks. rewrite eq_sym. apply dvector_size. apply gt0_k. trivial.  apply dRpermPres2. trivial.
             apply invPermPerm. apply findPermChecks.  rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.
             apply invPermPerm. apply findPermChecks. apply findPermChecks. rewrite composePermNeg. apply findPermChecks.
             rewrite permVectorID. apply dvector_size. apply gt0_k. trivial. trivial. apply commit_rand_ll.

   (* c0 *) congr. congr. congr. rewrite !bRing. rewrite -composePermA. apply invPermPerm. apply findPermChecks.
   apply findPermChecks. apply isPermSimp; trivial. rewrite composePermNeg. apply findPermChecks.
   rewrite composePermID; trivial. apply isPermSimp; trivial. 
   rewrite !bRing. rewrite -composePermA. apply invPermPerm. apply findPermChecks.
   apply findPermChecks. apply isPermSimp; trivial. rewrite composePermNeg. apply findPermChecks.
             rewrite composePermID; trivial. apply isPermSimp; trivial.
   rewrite !bRing. rewrite -composePermA. apply invPermPerm. apply findPermChecks.
   apply findPermChecks. apply isPermSimp; trivial. rewrite composePermNeg. apply findPermChecks.
             rewrite composePermID; trivial. apply isPermSimp; trivial.
     
             (* c1 *) congr. congr. congr. rewrite !bRing. rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.
             apply invPermPerm.
   apply findPermChecks. apply findPermChecks. rewrite composePermNeg. apply findPermChecks. 
   rewrite permVectorID. apply dvector_size. apply gt0_k. trivial. trivial. 
   rewrite !bRing. rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply invPermPerm.
   apply findPermChecks. apply findPermChecks. rewrite composePermNeg. apply findPermChecks. 
             rewrite permVectorID. apply dvector_size. apply gt0_k. trivial.  trivial.
   rewrite !bRing. rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial. apply invPermPerm.
   apply findPermChecks. apply findPermChecks. rewrite composePermNeg. apply findPermChecks. 
             rewrite permVectorID. apply dvector_size. apply gt0_k. trivial.  trivial.
     
             (* c2 *) congr. congr. congr. rewrite !bRing. rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.
             apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA.
    apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. 
    rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
    rewrite !bRing. rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA.
    apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. 
             rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
    rewrite !bRing. rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial. apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA.
    apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. 
    rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
     
     (* c3 *) congr. congr. congr. rewrite !bRing. apply t2_simp; trivial. rewrite size_addv. smt(@MLWE.M).
             rewrite bRing in g0. trivial.
     rewrite !bRing. apply t2_simp; trivial. rewrite size_addv. smt(@MLWE.M). rewrite bRing in g1. trivial.
     rewrite !bRing. apply t2_simp; trivial. rewrite size_addv. smt(@MLWE.M). rewrite bRing in g2. trivial.

     (* ts *) rewrite !bRing.  rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial.  rewrite -composePermA.
    apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. 
             rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
     rewrite !bRing. apply t2_simp; trivial. rewrite size_addv. smt(@MLWE.M). rewrite bRing in g0. trivial.
     rewrite !bRing.  rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial. apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial.  rewrite -composePermA.
    apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. 
             rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
             rewrite !bRing. apply t2_simp; trivial. rewrite size_addv. smt(@MLWE.M). rewrite bRing in g1. trivial.
     rewrite !bRing.  rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial.  rewrite -composePermA.
    apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. 
             rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
     rewrite !bRing. apply t2_simp; trivial. rewrite size_addv. smt(@MLWE.M). rewrite bRing in g2. trivial.


   (* c2 opening *) congr. congr. congr. rewrite !bRing.  rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.
    apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA.
    apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial. 
    rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
    rewrite !bRing.   rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA.
             apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial.
             rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
     rewrite !bRing.   rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA.
             apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial.
    rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
     
     rewrite !bRing. congr. congr. congr. rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA.
             apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial.
    rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
    rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA.
             apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial.
             rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
    rewrite composePermCorrect. apply dvector_size. apply gt0_k. trivial.  apply invPermPerm.
    apply findPermChecks. apply composePermPerm. apply findPermChecks. apply isPermSimp; trivial. rewrite -composePermA.
             apply invPermPerm. apply findPermChecks. apply findPermChecks. apply isPermSimp; trivial.
    rewrite composePermNeg. apply findPermChecks. rewrite composePermID.  apply isPermSimp; trivial.  trivial.
     
   (* c3 opening *) congr. congr. congr. rewrite !bRing. apply t2_simp; trivial. rewrite size_addv. smt(@MLWE.M).
             rewrite bRing in g0. trivial.
     rewrite !bRing. apply t2_simp; trivial. rewrite size_addv. smt(@MLWE.M). rewrite bRing in g1. trivial.
     rewrite !bRing. apply t2_simp; trivial. rewrite size_addv. smt(@MLWE.M). rewrite bRing in g2. trivial.
   qed.

     
     
lemma MulitRelProt_ZK s w e &m :
       R s w =>
       e \in range 0 3 =>
       islossless D.distinguish =>
       Pr[SHVZK(MultiRelProt, MultiRelAlg, D).simulate(s,e) @ &m : res] -
       Pr[SHVZK(MultiRelProt, MultiRelAlg, D).real(s,w,e) @ &m : res] <=
       Pr[HidingExperimentL(U(D)).main((s,w,e)) @ &m : res] -
       Pr[HidingExperimentR(U(D)).main((s,w,e)) @ &m : res].
     proof.
       move => @/R Rel Ran ll. rewrite (Real_GB_0 s w e &m); trivial.
       rewrite(Real_GB_1 s w e &m); trivial.
     qed.

lemma MultiRelProt_Completeness s w' &m:
  R s w' =>
  Pr[Completeness(MultiRelProt).main(s, w') @ &m  : res] = 1%r.
proof.
  move => @/R. move => h. have : rows s.`1 = k. smt(). move => h'.
  (* case e0*)
  byphoare (: arg = (s, w') ==> res) => //.
    conseq (: true ==> true: =1%r)(: arg = (s, w') ==> res). auto.
    (* correctness *)
  proc. inline MultiRelProt.test. swap [4..5] -3. seq 2 : ((x, w) = (s, w') /\ e \in range 0 3).
  auto. progress. smt(@List @Distr). case (e=0).
    (* case e = 0 *)
  inline *. rcondt 100. auto. progress. rcondt 119. auto. progress. auto. progress.

    (* case 0 - commitments*)
    rewrite -pairS. apply commit_verify_correct. rewrite -pairS. apply commit_verify_correct.
    rewrite -pairS. apply commit_verify_correct. 

    (* - perms *)
  apply isPermSimp; trivial.  apply isPermSimp; trivial.  apply isPermSimp; trivial. apply samplePerm4_def in H16.
elim H16 => [j0 [j1 [j2 j3]]]. trivial. apply samplePerm4_def in H16. elim H16 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H16. elim H16 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H16. elim H16 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H17. elim H17 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H17. elim H17 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H17. elim H17 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H17. elim H17 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H18. elim H18 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H18. elim H18 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H18. elim H18 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H18. elim H18 => [j0 [j1 [j2 j3]]]. trivial.
    (* Images *)
    apply e_0_simple; trivial. apply e_0_simple; trivial. apply e_0_simple; trivial.
    apply e_0_simple_j; trivial. apply e_0_simple_j; trivial. apply e_0_simple_j; trivial.
    (* Satisying the epected values *)
    apply subv_catvCr_ss. rewrite eq_sym. apply size_l. trivial. rewrite size_v_calc. trivial.
    apply subv_catvCr_ss. rewrite eq_sym. apply size_l. trivial. rewrite size_v_calc. trivial.
    apply subv_catvCr_ss. rewrite eq_sym. apply size_l. trivial. rewrite size_v_calc. trivial.
    (* size constrints *)
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply g8.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g4. apply g7.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g5. apply g7.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g6. apply g7.
    rewrite size_catv. rewrite size_v_calc. rewrite (dvector_size u10 l). apply gt0_l. trivial. trivial.
    rewrite size_catv. rewrite size_v_calc. rewrite (dvector_size u20 l). apply gt0_l. trivial. trivial.
    rewrite size_catv. rewrite size_v_calc. rewrite (dvector_size u30 l). apply gt0_l. trivial. trivial.
    rewrite size_addv. rewrite size_mulmxv. rewrite (dvector_size f10 k). apply gt0_k. trivial. trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g7. apply maxzz.
    rewrite size_addv. rewrite size_mulmxv. rewrite (dvector_size f20 k). apply gt0_k. trivial. trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g7. apply maxzz.
    rewrite size_addv. rewrite size_mulmxv. rewrite (dvector_size f30 k). apply gt0_k. trivial. trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g7. apply maxzz.
    apply permVectorSize. apply isPermSimp; trivial. apply permVectorSize. apply isPermSimp; trivial.
    apply permVectorSize. apply isPermSimp; trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 g16]]]]]]]]]]]]]]]]. apply g15.
  smt(R_sample_row). smt(R_sample_col). apply dRv4_v4 in H3.  elim H3 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H3.  elim H3 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H3.  elim H3 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H3.  elim H3 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H4.  elim H4 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H4.  elim H4 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H4.  elim H4 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H4.  elim H4 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H5.  elim H5 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H5.  elim H5 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H5.  elim H5 => [j0 [j1 [j2 j3]]]. trivial.
    apply dRv4_v4 in H5.  elim H5 => [j0 [j1 [j2 j3]]]. trivial.
    move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
    move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
    move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
   move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
    move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
    move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
    move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
   move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
    move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
    move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
   move => @/zerok4. simplify. move => @/max. rewrite gt0_k. simplify. trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H28. apply t0_4_k4_1; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H28. apply t0_4_k4_2; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H28. apply t0_4_k4_3; trivial. 
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H28. apply t0_4_k4_4; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H29. apply t0_4_k4_1; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H29. apply t0_4_k4_2; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H29. apply t0_4_k4_3; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H29. apply t0_4_k4_4; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H30. apply t0_4_k4_1; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H30. apply t0_4_k4_2; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H30. apply t0_4_k4_3; trivial. 
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H30. apply t0_4_k4_4; trivial.
  apply samplePerm4_def in H16. apply t1_4_k4_1; trivial. apply samplePerm4_def in H16. apply t1_4_k4_2; trivial.
  apply samplePerm4_def in H16. apply t1_4_k4_3; trivial. apply samplePerm4_def in H16. apply t1_4_k4_4; trivial.
  apply samplePerm4_def in H17. apply t1_4_k4_1; trivial. apply samplePerm4_def in H17. apply t1_4_k4_2; trivial.
  apply samplePerm4_def in H17. apply t1_4_k4_3; trivial. apply samplePerm4_def in H17. apply t1_4_k4_4; trivial.
  apply samplePerm4_def in H18. apply t1_4_k4_1; trivial. apply samplePerm4_def in H18. apply t1_4_k4_2; trivial.
  apply samplePerm4_def in H18. apply t1_4_k4_3; trivial. apply samplePerm4_def in H18. apply t1_4_k4_4; trivial.
  apply dRl4_l4 in H19. elim H19 => [j0 [j1 [j2 j3]]]. trivial.
  apply dRl4_l4 in H19. elim H19 => [j0 [j1 [j2 j3]]]. trivial.
  apply dRl4_l4 in H19. elim H19 => [j0 [j1 [j2 j3]]]. trivial.
  apply dRl4_l4 in H19. elim H19 => [j0 [j1 [j2 j3]]]. trivial.
  apply dRl4_l4 in H20. elim H20 => [j0 [j1 [j2 j3]]]. trivial.
  apply dRl4_l4 in H20. elim H20 => [j0 [j1 [j2 j3]]]. trivial.
apply dRl4_l4 in H20. elim H20 => [j0 [j1 [j2 j3]]]. trivial.
apply dRl4_l4 in H20. elim H20 => [j0 [j1 [j2 j3]]]. trivial.
apply dRl4_l4 in H21. elim H21 => [j0 [j1 [j2 j3]]]. trivial.
apply dRl4_l4 in H21. elim H21 => [j0 [j1 [j2 j3]]]. trivial.
apply dRl4_l4 in H21. elim H21 => [j0 [j1 [j2 j3]]]. trivial.
apply dRl4_l4 in H21. elim H21 => [j0 [j1 [j2 j3]]]. trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]]. apply g17.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]]. apply g16.

    (*case 1 *)
    case (e=1). inline *. rcondf 100. auto. progress. rcondt 100. auto. progress.
    rcondf 119. auto. progress. rcondt 119. auto. progress. auto. progress.
    rewrite -pairS. apply commit_verify_correct. rewrite -pairS. apply commit_verify_correct.
    rewrite -pairS. apply commit_verify_correct.  
    (* - perms *)
    apply isPermSimp; trivial.  apply isPermSimp; trivial.  apply isPermSimp; trivial.
  apply samplePerm4_def in H17. elim H17 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H17. elim H17 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H17. elim H17 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H17. elim H17 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H18. elim H18 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H18. elim H18 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H18. elim H18 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H18. elim H18 => [j0 [j1 [j2 j3]]]. trivial.
      apply samplePerm4_def in H19. elim H19 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H19. elim H19 => [j0 [j1 [j2 j3]]]. trivial.
    apply samplePerm4_def in H19. elim H19 => [j0 [j1 [j2 j3]]]. trivial.
  apply samplePerm4_def in H19. elim H19 => [j0 [j1 [j2 j3]]]. trivial.
    (* Images *)
    apply e_1_simple; trivial. elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g4. apply g7.
    apply e_1_simple; trivial. elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g5. apply g7.
    apply e_1_simple; trivial. elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g6. apply g7.
    apply e_1_simple_j; trivial. apply e_1_simple_j; trivial. apply e_1_simple_j; trivial.
    (* Satisying the epected values *)
    rewrite v_calc_addv4. rewrite (v_calc_swap_1 w{hr}.`1.`1 w{hr}.`1.`2 w{hr}.`1.`3 m11 m21 (x{hr}.`3 m11 m21)). trivial.
    apply dvector_size. apply gt0_4v. trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
    rewrite addv_catv. rewrite g9. apply dvector_size. apply gt0_l. trivial. rewrite subv_catvCr_ss.
    rewrite size_addv. rewrite g9. rewrite (dvector_size u10 l). apply gt0_l. trivial. apply maxzz.
    rewrite size_addv. rewrite size_v_calc. rewrite g10. apply maxzz. trivial.
    rewrite v_calc_addv4. rewrite (v_calc_swap_2 w{hr}.`1.`1 w{hr}.`1.`2 w{hr}.`1.`3 m11 m21 (x{hr}.`3 m11 m21)). trivial.
    apply dvector_size.  apply gt0_4v. trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
    rewrite addv_catv. rewrite g11. apply dvector_size. apply gt0_l. trivial. rewrite subv_catvCr_ss.
    rewrite size_addv. rewrite g11. rewrite (dvector_size u20 l). apply gt0_l. trivial. apply maxzz.
    rewrite size_addv. rewrite size_v_calc. rewrite g12. apply maxzz. trivial.
    rewrite v_calc_addv4. rewrite (v_calc_swap_3 w{hr}.`1.`1 w{hr}.`1.`2 w{hr}.`1.`3 m11 m21 (x{hr}.`3 m11 m21)); trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]]. apply g15.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
    rewrite addv_catv. rewrite g13. apply dvector_size. apply gt0_l. trivial. rewrite subv_catvCr_ss.
    rewrite size_addv. rewrite g13. rewrite (dvector_size u30 l). apply gt0_l. trivial. apply maxzz.
    rewrite size_addv. rewrite size_v_calc. rewrite g14. apply maxzz. trivial.
    apply (R_sample_valid w{hr}.`1.`1 w{hr}.`1.`2 w{hr}.`1.`3 m11 m21 (x{hr}.`3 m11 m21)). trivial.
    (* size constrints *)
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply g8.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g4. apply g7.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g5. apply g7.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g6. apply g7.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
    rewrite addv_catv. rewrite g9. apply dvector_size. apply gt0_l. trivial. rewrite size_catv. rewrite size_addv.
    rewrite size_addv. rewrite size_v_calc. rewrite g10. rewrite g9. rewrite (dvector_size _ l). apply gt0_l.
    trivial. rewrite !maxzz. trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
    rewrite addv_catv. rewrite g11. apply dvector_size. apply gt0_l. trivial. rewrite size_catv. rewrite size_addv.
    rewrite size_addv. rewrite size_v_calc. rewrite g12. rewrite g11. rewrite (dvector_size _ l). apply gt0_l.
    trivial. rewrite !maxzz. trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
    rewrite addv_catv. rewrite g13. apply dvector_size. apply gt0_l. trivial. rewrite size_catv.
    rewrite size_addv. rewrite size_addv. rewrite size_v_calc. rewrite g14. rewrite g13. rewrite (dvector_size _ l).
    apply gt0_l. trivial. rewrite !maxzz. trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
    rewrite size_addv. rewrite size_mulmxv. rewrite (dvector_size _ k). apply gt0_k. trivial. rewrite g7. apply maxzz.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
    rewrite size_addv. rewrite size_mulmxv. rewrite (dvector_size _ k). apply gt0_k.  trivial. rewrite g7. apply maxzz.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]].
    rewrite size_addv. rewrite size_mulmxv. rewrite (dvector_size _ k). apply gt0_k.  trivial. rewrite g7. apply maxzz.
    apply permVectorSize. apply isPermSimp; trivial. apply permVectorSize.  apply isPermSimp; trivial. apply permVectorSize.
     apply isPermSimp; trivial. 
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 g16]]]]]]]]]]]]]]]]. apply g15.
    smt(R_sample_row). smt(R_sample_col). 
    apply size_addv4_1; trivial. apply size_addv4_2; trivial. apply size_addv4_3; trivial. apply size_addv4_4; trivial.
    apply size_addv4_1; trivial. apply size_addv4_2; trivial. apply size_addv4_3; trivial. apply size_addv4_4; trivial.
    apply dRv4_v4 in H6. smt(size_addv4 subv4_v4).  
    apply dRv4_v4 in H6. smt(size_addv4 subv4_v4).  apply dRv4_v4 in H6. smt(size_addv4 subv4_v4).
    apply dRv4_v4 in H6. smt(size_addv4 subv4_v4). 
    apply  dW4size in H11. apply JKPT12commit4_size_1; trivial. apply  dW4size in H11. apply JKPT12commit4_size_2; trivial. 
    apply  dW4size in H11. apply JKPT12commit4_size_3; trivial. apply  dW4size in H11. apply JKPT12commit4_size_4; trivial. 
    apply  dW4size in H12. apply JKPT12commit4_size_1; trivial. apply  dW4size in H12. apply JKPT12commit4_size_2; trivial. 
    apply  dW4size in H12. apply JKPT12commit4_size_3; trivial. apply  dW4size in H12. apply JKPT12commit4_size_4; trivial. 
    apply  dW4size in H13. apply JKPT12commit4_size_1; trivial. apply  dW4size in H13. apply JKPT12commit4_size_2; trivial. 
    apply  dW4size in H13. apply JKPT12commit4_size_3; trivial. apply  dW4size in H13. apply JKPT12commit4_size_4; trivial. 

  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H29. apply t0_4_k4_1; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H29. apply t0_4_k4_2; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H29. apply t0_4_k4_3; trivial. 
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H29. apply t0_4_k4_4; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H30. apply t0_4_k4_1; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H30. apply t0_4_k4_2; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H30. apply t0_4_k4_3; trivial. 
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H30. apply t0_4_k4_4; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H31. apply t0_4_k4_1; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H31. apply t0_4_k4_2; trivial.
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H31. apply t0_4_k4_3; trivial. 
  elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply dRk4_k4 in H31. apply t0_4_k4_4; trivial.
  apply samplePerm4_def in H17. apply t2_4_k4_1; trivial. apply samplePerm4_def in H17. apply t2_4_k4_2; trivial. 
  apply samplePerm4_def in H17. apply t2_4_k4_3; trivial.  apply samplePerm4_def in H17. apply t2_4_k4_4; trivial. 
  apply samplePerm4_def in H18. apply t2_4_k4_1; trivial.  apply samplePerm4_def in H18. apply t2_4_k4_2; trivial. 
  apply samplePerm4_def in H18. apply t2_4_k4_3; trivial.  apply samplePerm4_def in H18. apply t2_4_k4_4; trivial. 
  apply samplePerm4_def in H19. apply t2_4_k4_1; trivial.  apply samplePerm4_def in H19. apply t2_4_k4_2; trivial. 
  apply samplePerm4_def in H19. apply t2_4_k4_3; trivial.  apply samplePerm4_def in H19. apply t2_4_k4_4; trivial. 
  apply size_addl4_1; trivial. apply size_addl4_2; trivial. apply size_addl4_3; trivial. apply size_addl4_4; trivial.
    apply size_addl4_1; trivial. apply size_addl4_2; trivial. apply size_addl4_3; trivial. apply size_addl4_4; trivial.
  apply size_addl4_1; trivial. apply size_addl4_2; trivial. apply size_addl4_3; trivial. apply size_addl4_4; trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]]. apply g17.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]]. apply g16.

   (* case 2 - commitments*)
    seq 0 : ((x, w) = (s, w') /\ (e \in range 0 3) /\ e =2). auto. progress. smt(@Int @List). inline *.
    rcondf 100. auto. progress. rcondf 100. auto. progress.
    rcondf 119. auto. progress. rcondf 119. auto. progress. rcondt 119. auto. progress. auto. progress.
    rewrite -pairS. apply commit_verify_correct. rewrite -pairS. apply commit_verify_correct.
    (* check w *)
    apply checkWHelp; trivial. apply dvector_size. apply gt0_k. trivial. rewrite size_addv. rewrite size_oppv.
    rewrite size_mulmxv. elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]].
    rewrite g4. rewrite g7. apply maxzz. trivial. trivial. elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply g0.
    apply checkWHelp; trivial. apply dvector_size. apply gt0_k. trivial. rewrite size_addv. rewrite size_oppv.
    rewrite size_mulmxv. elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]].
    rewrite g5. rewrite g7. apply maxzz. trivial. trivial. elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply g1.
    apply checkWHelp; trivial. apply dvector_size. apply gt0_k. trivial. rewrite size_addv.
    rewrite size_oppv. rewrite size_mulmxv. elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]].
    rewrite g6. rewrite g7. apply maxzz. trivial. trivial. elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply g2.
    apply checkWHelp2_1; trivial. apply checkWHelp2_2; trivial. apply checkWHelp2_3; trivial. apply checkWHelp2_4; trivial. apply checkWHelp2_1; trivial. apply checkWHelp2_2; trivial. apply checkWHelp2_3; trivial. apply checkWHelp2_4; trivial. apply checkWHelp2_1; trivial. apply checkWHelp2_2; trivial. apply checkWHelp2_3; trivial. apply checkWHelp2_4; trivial.

    (* Commitments valid *)
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply JKPT12commit4_corr; trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply JKPT12commit4_corr; trivial.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply JKPT12commit4_corr; trivial.
    rewrite compact_subv4. apply dvector_size. apply gt0_4v. trivial. rewrite compact_subv4.
    apply dvector_size. apply gt0_4v. trivial. trivial.
    (* size constrints *)
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. apply g8.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g4. apply g7.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g5. apply g7.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 g9]]]]]]]]]. rewrite g6. apply g7.
    smt(gt0_l gt0_v). smt(gt0_l gt0_v). smt(gt0_l gt0_v). apply permVectorSize. apply isPermSimp; trivial. 
    apply permVectorSize. apply isPermSimp; trivial. apply permVectorSize. apply isPermSimp; trivial. 
    apply permVectorSize. apply isPermSimp; trivial.  apply permVectorSize. apply isPermSimp; trivial. 
    apply permVectorSize. apply isPermSimp; trivial. 
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]]. apply g15.
    smt(gt0_v). smt(gt0_v). apply subv4_s1. apply subv4_s2. apply subv4_s3. apply subv4_s4.
    apply subv4_s1. apply subv4_s2. apply subv4_s3. apply subv4_s4.
    apply subv4_s1. apply subv4_s2. apply subv4_s3. apply subv4_s4.
    apply  dW4size in H10. apply JKPT12commit4_size_1; trivial.  apply  dW4size in H10. apply JKPT12commit4_size_2; trivial. 
    apply  dW4size in H10. apply JKPT12commit4_size_3; trivial. apply  dW4size in H10. apply JKPT12commit4_size_4; trivial. 
    apply  dW4size in H11. apply JKPT12commit4_size_1; trivial.  apply  dW4size in H11. apply JKPT12commit4_size_2; trivial. 
    apply  dW4size in H11. apply JKPT12commit4_size_3; trivial. apply  dW4size in H11. apply JKPT12commit4_size_4; trivial.
    apply  dW4size in H12. apply JKPT12commit4_size_1; trivial.  apply  dW4size in H12. apply JKPT12commit4_size_2; trivial. 
    apply  dW4size in H12. apply JKPT12commit4_size_3; trivial. apply  dW4size in H12. apply JKPT12commit4_size_4; trivial.
   
  apply samplePerm4_def in H16. apply t1_4_k4_1; trivial. apply samplePerm4_def in H16. apply t1_4_k4_2; trivial.
  apply samplePerm4_def in H16. apply t1_4_k4_3; trivial. apply samplePerm4_def in H16. apply t1_4_k4_4; trivial.
  apply samplePerm4_def in H17. apply t1_4_k4_1; trivial. apply samplePerm4_def in H17. apply t1_4_k4_2; trivial.
  apply samplePerm4_def in H17. apply t1_4_k4_3; trivial. apply samplePerm4_def in H17. apply t1_4_k4_4; trivial.
  apply samplePerm4_def in H18. apply t1_4_k4_1; trivial. apply samplePerm4_def in H18. apply t1_4_k4_2; trivial.
  apply samplePerm4_def in H18. apply t1_4_k4_3; trivial. apply samplePerm4_def in H18. apply t1_4_k4_4; trivial.
  
  apply samplePerm4_def in H16. apply t2_4_k4_1; trivial. apply samplePerm4_def in H16. apply t2_4_k4_2; trivial. 
  apply samplePerm4_def in H16. apply t2_4_k4_3; trivial.  apply samplePerm4_def in H16. apply t2_4_k4_4; trivial. 
  apply samplePerm4_def in H17. apply t2_4_k4_1; trivial.  apply samplePerm4_def in H17. apply t2_4_k4_2; trivial. 
  apply samplePerm4_def in H17. apply t2_4_k4_3; trivial.  apply samplePerm4_def in H17. apply t2_4_k4_4; trivial. 
  apply samplePerm4_def in H18. apply t2_4_k4_1; trivial.  apply samplePerm4_def in H18. apply t2_4_k4_2; trivial. 
  apply samplePerm4_def in H18. apply t2_4_k4_3; trivial.  apply samplePerm4_def in H18. apply t2_4_k4_4; trivial. 
  apply subl4_s1. apply subl4_s2. apply subl4_s3. apply subl4_s4.
  apply subl4_s1. apply subl4_s2. apply subl4_s3. apply subl4_s4.
  apply subl4_s1. apply subl4_s2. apply subl4_s3. apply subl4_s4.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]]. apply g17.
    elim: h => [g0 [g1 [g2 [g3 [g4 [g5 [g6 [g7 [g8 [g9 [g10 [g11 [g12 [g13 [g14 [g15 [g16 g17]]]]]]]]]]]]]]]]]. apply g16.

    (* termination *)
    proc. inline *. auto. progress. apply keygen_ll. smt(dR_ll @MLWE.M).  apply dRv4_ll. apply R_sample_ll. smt(dR_ll @MLWE.M).
    apply dW4_ll. apply duniform_ll. apply permNotEmpty. apply perm4_ll. apply dRl4_ll. smt(dR_ll @MLWE.M).
    smt(dR_ll @MLWE.M). apply dRk4_ll. apply commit_rand_ll. apply duniform_ll. rewrite range_ltn. smt(@Int). smt().
qed.
   
