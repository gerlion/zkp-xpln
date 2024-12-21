require import AllCore Distr DInterval  IntDiv List Perms Binomial Logic.

require (*--*) Commitment.

require (*--*) SigmaProtocol3.
require (*--*) MLWE.

import MLWE.
import M.
import ZR.
    
(* the lenght of the messages the commitment scheme will handle *)
op v : { int | 0 < v } as gt0_v.


lemma dProdMatrixSize a : 
  a \in dmatrix dR k l `*` dmatrix dR k v => size (a.`1||a.`2) = (k,l+v).
proof.
  move => h. rewrite size_catmr. have : a.`1 \in dmatrix dR k l /\ a.`2 \in dmatrix dR k v.
  smt(@Distr). move => h'. elim h' => h' h''. apply size_dmatrix in h'. apply size_dmatrix in h''.
  smt(gt0_v gt0_k gt0_l @M).
qed.

(* Since we work mod 2 every vector is it's own inverse *)
axiom twoElements : forall (v : t), v = zeror \/ v = oner.

lemma bRing_t : forall (v : t), - v = v.
proof.
  smt(@M twoElements).
qed.

lemma bRing : forall (v : vector), -v = v.
proof.
  move => v. apply eq_vectorP. smt(@M bRing_t).
qed.

(* Hamming weight *)
op weight v = count (fun x => x <> zeror) (tolist v).

(* the hamming distance of the noise vector *)
op w : {int | 0 <= w } as ge0_w.
axiom chi_weight x : x \in chi => weight x = w.

op checkW v = weight v = w.

(* The Hamming weight of two vectors added together is bounded by the sum of weight of the two vectors *)
lemma weightAdd_sub1 (x y : t list) i : (nth zeror x i + nth zeror y i) <> zeror =>
    nth zeror x i <> zeror \/ nth zeror y i <> zeror.
proof.
move => h. case (nth zeror x i =  zeror) => h'. case (nth zeror y i =  zeror) => h''.
  have : nth zeror x i + nth zeror y i = zeror. smt(@ZR).
  smt(@M). right. trivial. left. trivial. 
qed.

lemma weightAdd_sub2_sub f x y :  f == (fun (i : int) => nth zeror x i + nth zeror y i) =>
    forall s, 0 <= s =>
   count (fun (i : t) => i <> zeror) (mkseq f s) <=
   count (fun (i : t) => i <> zeror) (take s x) +
   count (fun (i : t) => i <> zeror) (take s y).
proof. 
  move => hf. apply intind. simplify. smt(@List).
  simplify. move => j hj hind.  rewrite -(take_size (mkseq f (j+1))). rewrite size_mkseq.
   have :  (max 0 (j + 1)) = j + 1. smt(). move => g. rewrite g.
  rewrite (take_nth zeror). smt(@List). rewrite -!cats1.  rewrite !count_cat.
  rewrite !take_mkseq. smt().
  (* cases *)
  case (j < size x) => h.  rewrite (take_nth zeror). smt(@List).
  case (j < size y) => h'.  rewrite (take_nth zeror). smt(@List).
  rewrite -!cats1. rewrite !count_cat.
  rewrite nth_mkseq. smt(). rewrite hf. 
  have : forall (a b c d e f : int), a <= b + c => d <= e + f =>  a + d <= b + e + (c + f). smt().
  move => g'. apply g'. trivial. smt(weightAdd_sub1). rewrite (take_oversize _ y). smt().
  rewrite -!cats1.  rewrite !count_cat. rewrite nth_mkseq. smt(). rewrite hf.
  rewrite (nth_default _ y). smt(). smt(@ZR @List). rewrite (take_oversize _ x). smt().
  case (j < size y) => h'.  rewrite (take_nth zeror). smt(@List).
  rewrite -!cats1.  rewrite !count_cat. rewrite nth_mkseq. smt(). rewrite hf.
  rewrite (nth_default _ x). smt(). smt(@ZR @List). rewrite (take_oversize _ y). smt().
  rewrite nth_mkseq. smt(). rewrite hf. rewrite !nth_default. smt(). smt(). smt(@ZR @List).
qed.    

lemma weightAdd_sub2 (x y : t list) f s:
    f ==  (fun (i : int) => nth zeror x i + nth zeror y i) =>
    s = (max (size x) (size y)) =>
    count (fun i, i <> zeror) (mkseq f s) <=
    count  (fun i, i <> zeror) x + count  (fun i, i <> zeror) y.
proof.
  move => hf hs. 
  rewrite -(take_size x). rewrite -(take_size y).
  have : take (size x) x = take s x. smt(@List). move => g'. rewrite g'.
  have : take (size y) y = take s y. smt(@List). move => g''. rewrite g''. apply weightAdd_sub2_sub.
  smt(). smt(@List).
qed.
  
lemma weightAdd : forall (x y : vector), weight (x + y) <= weight x + weight y.
proof.
  move => @/weight @/tolist x y. have : map (fun (i : int) => (x + y).[i]) (range 0 (size (x + y))) =
  mkseq (fun (i : int) => (x + y).[i]) (size (x + y)). smt(@List). move => g. rewrite g.
  apply weightAdd_sub2. simplify.  move => i. case (0 <= i) => h.
  case (i < size x) => h'. rewrite (nth_map 0). smt(@List). rewrite nth_range. smt(@List).
  case (i < size y) => h''. rewrite (nth_map 0). smt(@List). rewrite nth_range. smt(@List). smt(@M).
  rewrite nth_default. smt(@List). smt(@M). rewrite nth_default. smt(@List).
  case (i < size y) => h''.  rewrite (nth_map 0). smt(@List). rewrite nth_range. smt(@List). smt(@M).
  rewrite nth_default. smt(@List). smt(@M). smt(@M @List). smt(@List @M).
qed.

lemma weightSub : forall (x y : vector), weight (x - y) <= weight x + weight y.
    move => x y. rewrite bRing. apply weightAdd. qed.
  
(* mDist denotes the probability that a randomly choosen matrix has distance larger than 2w *)
op mDist (k l v :int ) : real.  
axiom aDistance : mu (dmatrix dR k l `*` dmatrix dR k v)
  (fun (x : matrix * matrix) => forall (y y' : vector),
   w + w < weight ((x.`1 || x.`2) *^ y - (x.`1 || x.`2) *^ y') /\
   (x \in dmatrix dR k l `*` dmatrix dR k v)) =
1%r - mDist k l v.
  
(* This commitment scheme needs to take permutations and vectors so we define a mapping function *)
  op permToVector : int list -> vector.
  op vectorToPerm : vector -> int list.
  axiom permToVectorInj p p' : permToVector p = permToVector p' => p = p'.

  lemma permToVectorInj3 p0 p1 p2 p0' p1' p2' :
    (permToVector p0, permToVector p1, permToVector p2) =
      (permToVector p0', permToVector p1', permToVector p2') => (p0,p1,p2) = (p0',p1',p2').
  proof.
    smt(permToVectorInj).
  qed.

  lemma permToVectorInj3_4 p0 p1 p2 p0' p1' p2' :
    (permToVector p0, permToVector p1, permToVector p2, zerov 0) =
    (permToVector p0', permToVector p1', permToVector p2', zerov 0) => (p0,p1,p2) = (p0',p1',p2').
  proof.
    smt(permToVectorInj).
  qed.  
      
  lemma permToVectorInj4 p0 p1 p2 p3 p0' p1' p2' p3':
    (permToVector p0, permToVector p1, permToVector p2, permToVector p3) =
      (permToVector p0', permToVector p1', permToVector p2', permToVector p3') =>
      (p0,p1,p2,p3) = (p0',p1',p2',p3').
  proof.
    smt(permToVectorInj).
  qed.

  (* Now we build up more lemmas about permuations and vectors *)
  op isPerm_n (pi : int list) n : bool = perm_eq pi (range 0 n).
  op isPerm (pi : int list) : bool = isPerm_n pi k.
  op permID = range 0 k.

  lemma perm_ind (p:int list -> bool):
    (p []) =>
    (forall i, 0 <= i => (forall l, isPerm_n l i => p l) => (forall l, isPerm_n l (i+1) => p l)) =>
    (forall i, 0 <= i => forall l, isPerm_n l i => p l).
  proof.
    move => h0 hind. apply intind. smt(@List). move => i hi hind'. simplify. apply hind. trivial. apply hind'.
  qed.

  lemma perm_rem_ind l i : 0 <= i =>
    isPerm_n l (i+1) => isPerm_n (rem i l) i.
  proof.
    move => hi @/isPerm_n h. smt(@List).
  qed.

  lemma perm_eq_nth pi n j : 0 < n => isPerm_n pi n => 
      0 <= nth 0 pi j && nth 0 pi j < size pi.
   proof.
     move => @/isPerm_n hn h. smt(@List).
 qed.

  lemma perm_eq_index pi n j : 0 < n => 0 <= j < n => isPerm_n pi n =>
     index j pi \in pi.
  proof.
    move => @/isPerm_n hn hj h. have : 0 <= index j pi < n. split. smt(@List). move => h'.
    have : n = size pi. smt(@List). move => h''. rewrite h''. rewrite index_mem. smt(@List). smt(@List).
  qed.

  lemma isPerm_n_size pi n : 0 <= n => isPerm_n pi n => size pi = n.
  proof.
  move => @/isPerm_n isPerm. smt(@List).
  qed.

  lemma perm_eq_trim (v : R list) j : 0 <= j < size v =>
     perm_eq v ((trim v j) ++ [nth zeror v j]).  
  proof.
    move => @/trim. move => h. rewrite perm_eq_sym. apply perm_catAC. apply perm_eq_refl_eq. smt(@List).
qed.

  lemma perm_eq_trim2 (v : R list) j : 0 <= j < size v =>
     perm_eq v (nth zeror v j :: (trim v j)).  
  proof.
    move => @/trim. move => h. rewrite perm_eq_sym. rewrite -cat_cons. apply perm_eq_nth_take_drop.
    trivial.
  qed.

  lemma isPerm_size_k pi : isPerm pi => size pi =k.
  proof.
    move => isPerm. smt(@Perms @List gt0_k).
  qed.    
  
  lemma isPermSimp pi : pi \in duniform (allperms (range 0 k)) => isPerm pi.
  proof.
    smt(@Distr @Perms @List).
  qed.
  
  lemma isPermSimp2 pi : isPerm pi => pi \in duniform (allperms (range 0 k)).
  proof.
    smt(@Distr @Perms @List).
  qed.
  
  op permVector (v : vector) (pi : int list) : vector = 
    oflist (map (fun i => nth ZR.zeror (tolist v) (nth 0 pi i)) (range 0 (size pi))).

  lemma rem_nth ['a] (a:'a) (i : 'a) l :
    forall j, 0 <= j => nth a (rem i l) j = nth a l (if j < index i l then j else j + 1).
    elim l. smt().
    move => x l hind j hj. simplify. rewrite index_cons. case (i=x) => h. rewrite h. simplify. have : !(j < 0). smt().
      move => h'. rewrite h'. simplify. have : j +1 <> 0. smt(). move => g. rewrite g. simplify.  trivial.
      have : x<>i. smt(). move => h'. rewrite h'. simplify. case (j < index i l + 1) => g. case (j=0) => g'. trivial.
    rewrite hind. smt(). smt(). have : j <> 0. smt(@List). move => g'. rewrite g'. have : j +1 <> 0. smt(@List).
    move => g''. rewrite g''. simplify. rewrite hind. smt(). smt().
  qed.

 op invPerm_n (pi : int list) n : int list = map (fun i : int => index i pi) (range 0 n).
 op invPerm pi = invPerm_n pi k.
 
    lemma permCount x v : isPerm v => count (pred1 x) v <= 1.
  proof.
    move => @/ isPerm h. have : count ((=) x) (range 0 k) <= 1.
    have : uniq (range 0 k). smt(@List). move => h''. case (x \in (range 0 k)); move => h'.
    have : count (pred1 x) (range 0 k) = 1. rewrite count_uniq_mem; trivial. smt(). move => g. smt(@List).
    smt(@List). smt(@List).
  qed.

  lemma invPermMem x v n :isPerm_n v n => x \in invPerm_n v n  <=> x \in range 0 n.
  proof.
    move => @/invPerm @/isPerm h'. split; move => h.
    (* case 1 *)
    rewrite (mapP _ (range 0 n) x) in h. elim h.  simplify. move => x0 h.
    have : 0 <= x. smt(@List @Int). move => g. have : x < n.  have : size v = n.  smt(@List). move => g'.
    rewrite -g'. elim h. move => h h''.  rewrite h''. smt(@List). smt(@List). 
    (* case 2 *)
    rewrite mapP. exists (nth 0 v x). split. smt(@List). simplify. smt(@List @Int).
  qed. 

  lemma invPermPerm v n : isPerm_n v n => isPerm_n (invPerm_n v n) n.
  proof.
    move => @/isPerm @/isPerm_n h. apply allP. move => x h'. simplify. have : x \in invPerm_n v n = x \in range 0 n.
    rewrite (invPermMem x v); trivial. move => g. have : x \in range 0 n. smt(@List). move => g'.
    have : count (pred1 x) (range 0 n) = 1. smt(@List). move => g''. rewrite g''. move => @/invPerm.
    have : count (pred1 x) v = 1. smt(@List). move => h''.
    have : uniq (map (fun (i : int) => index i v) (range 0 n)). apply map_inj_in_uniq. move => y z c c'.
    simplify. move => h'''. smt(@List). smt(@List).  move => l.
    have : x \in  (map (fun (i : int) => index i v) (range 0 n)). clear h' g g'' h''. apply mapP.
    exists (nth 0 v x). split. smt(@List). simplify. smt(@List @Int). move => @/invPerm_n. smt(@List).
qed.

lemma perm_invPerm pi n i: isPerm_n pi n => 0<= i < n => index i pi = nth 0 (invPerm_n pi n) i.
proof.
  move => isP hi @/invPerm_n. rewrite (nth_map 0). smt(@List). rewrite nth_range. smt(). trivial.
qed.

lemma trim_map ['a 'b] (b : 'b) (f : 'a -> 'b) (l : 'a list) n : trim (map f l) n = map f (trim l n).
proof.
  apply (eq_from_nth b). smt(@List). smt(@List).
qed.

lemma map_count ['a 'b] x (f : 'a -> 'b) (l : 'a list) :
    count (pred1 x) (map f l) = count (fun y => x = f y) l.
 proof.
   elim l. trivial. move => y l hind. simplify. rewrite hind. smt().
qed.

lemma perm_in_count ['a] (a : 'a) x v pi :
    count (pred1 x) (map (fun (i : int) => nth a v i) pi) = count (fun y => x = nth a v y) pi.
 proof.
   apply map_count.
qed.

(* If you permuate a permuation by a permutation the result is equal up to permuation to the orgional perm *)
lemma perm_eq_sub ['a] (a : 'a) j pi (v : 'a list) :  size v = j => isPerm_n pi j =>
    perm_eq (map (fun (i : int) => nth a v i) pi) v. 
 proof.
   move => size_v isPerm_pi. apply perm_eqP_pred1. move => x. simplify.
   rewrite (perm_in_count a x v pi).
   have : count (fun (y : int) => x = nth a v y) pi = count (fun (y : int) => x = nth a v y) (range 0 j).
   apply perm_eqP. smt(@List). move => h. rewrite h. rewrite -perm_in_count. smt(@List).
qed.

(* If one vetor is the permutation of another they are equal up to permutation  *)
lemma perm_eq_permVector_sub j pi : 0 <= j => isPerm_n pi j =>
    forall (v v' : R list),
    v' = (map (fun (i : int) => nth zeror v (nth 0 pi i))(range 0 (size pi))) =>
    size v = size pi =>
    perm_eq v v'.
proof.
  move => ge0_j isPerm_pi v v' hv size_v. rewrite hv. rewrite perm_eq_sym.
  have : map (fun (i : int) => nth zeror v (nth 0 pi i)) (range 0 (size pi)) = map (fun (i : int) => nth zeror v i) pi.
  apply (eq_from_nth zeror). smt(@List). move => i hi. rewrite !(nth_map 0). smt(@List). smt(@List). rewrite nth_range. smt(@List).
  trivial.  move => h. rewrite h. apply (perm_eq_sub zeror j pi v). rewrite size_v. apply isPerm_n_size; trivial. trivial.
qed.

  lemma perm_eq_permVector (v : vector) pi : isPerm pi => size v = k =>
    perm_eq (tolist v) (tolist (permVector v pi)).  
  proof.
    move => hpi sv_k. rewrite oflistK. have : (0 <= k). smt(gt0_k). move => g.
    apply (perm_eq_permVector_sub k pi g); trivial. smt(@M @List).
  qed.

  lemma permVectorSize v pi : isPerm pi => size (permVector v pi) = k.
  proof.
    move => @/isPerm @/isPerm_n h. rewrite size_oflist. rewrite size_map. smt(@List gt0_k).
  qed.
  
  lemma mu1_dvector_fu_gen (d: R distr) s (v: vector): is_funiform d => s = size v =>
    mu1 (dvector d s) v = (mu1 d witness)^s.
  proof.
    move =>un sizeV. rewrite sizeV. apply mu1_dvector_fu. trivial.
  qed.
      
  lemma dRpermPres : forall (v : vector) pi, isPerm pi => k = size v =>
    mu1 (dvector dR k) v =
    mu1 (dvector dR k)(permVector v pi).
  proof.
    move => v pi isPerm sizeK. rewrite !mu1_dvector_fu_gen; trivial. apply dR_funi. apply dR_funi.
    rewrite permVectorSize. trivial. trivial.
  qed.

  lemma dRmu1ss : forall s (v v' : vector),
    size v = s => size v' = s =>
    mu1 (dvector dR s) v =
    mu1 (dvector dR s) (v + v').
  proof.
    move => s v v' sizeS sizeS'. rewrite !mu1_dvector_fu_gen; trivial. apply dR_funi. smt(). apply dR_funi. smt(@M). 
  qed.
  
  lemma dRmu1ins : forall s (v v' : vector), 0 < s =>
    v \in dvector dR s => size v' = s =>
    mu1 (dvector dR s) v =
    mu1 (dvector dR s) (v + v').
  proof.
    move => s v v' gt0_s sizeS sizeS'. rewrite !mu1_dvector_fu_gen; trivial. apply dR_funi. smt(@M). apply dR_funi. smt(@M).
  qed.
    
  lemma dRin : forall s (v : vector),
    size v = s =>
      v \in dvector dR s.
  proof.
    move => s v size. rewrite -size. apply dvector_fu. smt(@Distr dR_funi dR_ll).
  qed.
    
  lemma dvector_size : forall s v, 0 <= s =>
    v \in dvector dR s => size v = s.
   proof.
     move => s v s_g0 inS. rewrite (supp_dvector dR v s s_g0) in inS. smt().
   qed.
  
  lemma dRpermPres2 : forall v pi,
    v \in dvector dR k => isPerm pi =>
    permVector v pi \in dvector dR k.
  proof.
    move => v pi ink isPerm. rewrite -(permVectorSize v pi). trivial. apply dvector_fu.  smt(@Distr dR_funi dR_ll).
  qed.
  
  lemma permVectorID (v : vector) : size v = k => permVector v permID = v.
  proof.
    move => h. apply eq_vectorP. split. smt(gt0_k @MLWE.M @List).
    move => i h'. rewrite (get_oflist ZR.zeror). smt(@List @MLWE.M gt0_k). rewrite (nth_map 0).  smt(@List @MLWE.M gt0_k).
    simplify. rewrite (nth_range i). smt(@List @MLWE.M gt0_k). simplify. rewrite (nth_range i). smt(@List @MLWE.M gt0_k).
    apply nth_tolist. smt(@MLWE.M @List gt0_k).
  qed.

  (* defining what it means for a perumtation to map between two vector *)
  op permEq_n (v v' : vector) pi n =  size v = size v' /\ isPerm_n pi n /\ v = permVector v' pi .
  op permEq (v v' : vector) pi =  permEq_n v v' pi k.

  (* two verctors are equal upto permutation if such a permutation exists *)
  op arePermEq_n v v' n = exists pi, permEq_n v v' pi n.
  op arePermEq v v' =  arePermEq_n v v' k.
  
  op findPermEq (v v' :vector) : int list = choiceb (permEq v v') (permID).
  
  lemma findPermChecks v v' : isPerm (findPermEq v v').
  proof.
    case(exists x, permEq v v' x) => h. smt(choicebP). move => @/findPermEq. rewrite choiceb_dfl. smt().
    smt(@List).
  qed.
      
  lemma findPermSize v v' : size (findPermEq v v') = k.
  proof.
    apply isPerm_size_k. apply findPermChecks.
  qed.

  (* If a permuation exists then findPermEq returns it *)
  lemma findPermCorr v v' : arePermEq v v' => v = permVector v' (findPermEq v v').
  proof.
    move => h. smt(choicebP).
  qed.

  lemma count_rearrange ['a] (x : 'a)  xs ys p : count p (x :: xs) = count p ys => count p xs = count p ys - (b2i (p x)).
  proof.
    smt(@List).
  qed.

  lemma weightInv (v v' : vector) : size v = size v' => weight v = weight v' =>
    count (pred1 zeror) (tolist v) = count (pred1 zeror) (tolist v').
      move => @/weight size_v_v'  w_eq. have : predC (pred1 zeror) = (fun (x : t) => x <> zeror). smt(). smt(@List).
    qed.


  (* If two lists are equal up to permutation then there must exist a permutation between them *)
  lemma perm_eq_to_PermEq_sub : forall j, 0 <= j => forall (v v' : t list), size v = j => perm_eq v v' =>
    exists pi, isPerm_n pi j /\ v = (map (fun i => nth ZR.zeror v' (nth 0 pi i)) (range 0 (size pi))).
  proof.
    apply intind. simplify. move => v v' size_v perm_eq_v. exists []. smt(@List @M).
    simplify. move => i hi hind. move => v v' size_v perm_eq_v.
    have : exists pi, isPerm_n pi i /\
  behead v =  map (fun (i1 : int) => nth zeror (rem (head zeror v) v') (nth 0 pi i1)) (range 0 (size pi)).
    apply hind. smt(@List). smt(@List). elim => pi [hpi hperm].

   (* define the larger permutation in terms of the smaller *)
    exists ((index (head zeror v) v') ::
    map (fun i => if i < index (head zeror v) v' then i else i+1) pi). split.

    (* it is a permutation *)
  move => @/isPerm_n. have : perm_eq pi (range 0 i). smt(). move => g.
    pose s := range 0 (i +1). pose n := (index (head zeror v) v').
    rewrite (perm_eq_trans (nth 0 s n :: take n s ++ drop (n + 1) s)). rewrite nth_range. smt(@List).
    simplify. apply perm_cons. apply allP. move => x hx. simplify. 
    rewrite map_count. rewrite (perm_eqP pi (range 0 i)) in g. rewrite g. move => @/s @/n.
    rewrite -map_count. congr. apply (eq_from_nth 0). rewrite size_cat. rewrite size_take.
    smt(@List). have : index (head zeror v) v' < size (range 0 (i + 1)). smt(@List). move => g'.
    rewrite g'. simplify. rewrite size_map. rewrite size_drop. smt(@List). smt(@List).
  move => j hj. rewrite (nth_map 0). smt(@List). rewrite nth_cat. rewrite size_take.
    smt(@List). have : index (head zeror v) v' < size (range 0 (i + 1)). smt(@List). move => g'.
    rewrite g'. rewrite nth_range. rewrite size_map in hj. smt(@List). simplify.
    case (j < index (head zeror v) v') => g''. rewrite nth_take. smt(@List). trivial. smt(@List).
    rewrite nth_drop. smt(@List). smt(@List). rewrite nth_range. split. smt(). move => h.
    simplify. rewrite size_map in hj. rewrite size_range in hj. smt(). smt().
    apply perm_eq_nth_take_drop. smt(@List).
  
    (* it works *)
    rewrite -(head_behead v zeror). smt(@List). rewrite hperm. apply (eq_from_nth zeror). smt(@List).
    simplify. move => j hj. rewrite eq_sym.
    simplify. rewrite (nth_map 0). smt(@List). rewrite nth_range. smt(@List). simplify.
    case (j=0) => g. smt(@List). rewrite !(nth_map 0). smt(@List). smt(@List perm_eq_nth).
    simplify. rewrite nth_range. smt(@List perm_eq_nth). rewrite rem_nth. smt(@List perm_eq_nth).
    simplify. trivial.
  qed.
  
  (* If two lists are equal up to permutation then there must exist a permutation between them *)
  lemma perm_eq_to_PermEq v v' : perm_eq (tolist v) (tolist v') => arePermEq_n v v' (size v). 
  proof.
  move => h. have : 0 <= size v. smt(@M). move => g.
    have : exists pi, isPerm_n pi (size v) /\ (tolist v) =
  (map (fun i => nth ZR.zeror (tolist v') (nth 0 pi i)) (range 0 (size pi))). apply perm_eq_to_PermEq_sub. smt(). smt(@M). trivial.
  elim => pi hpi. exists pi. split. smt(@List @M). split; trivial. smt(). move => @/permVector.  rewrite -hpi. smt(@M).
  qed.
  
  (* Every vector of the same weight is equal up to permutation *)
  lemma permEqWeight : forall j, 0 <= j => forall (v v' : vector), size v = j => size v' = j => weight v = weight v' => arePermEq_n v v' j.
  proof.
    move => @/weight j hj v v' size_v size_v' w_eq. have: perm_eq (tolist v) (tolist v'). apply allP. move => x hx. simplify.

    elim (twoElements x) => g; rewrite g.
    (* case where the element being counted is zero *)
    smt( weightInv).
  
   (* case where the element being counted is one *)
  rewrite (eq_in_count (pred1 oner) (fun x => x<>zeror)). move => x0 x0h. elim (twoElements x0); smt(@M). trivial.
   rewrite w_eq. rewrite (eq_in_count (pred1 oner) (fun x => x <> zeror)).
    move => x0 x0h. elim (twoElements x0); smt(@M). trivial. move => g.

   apply perm_eq_to_PermEq in g. smt().
  qed.
      
  op composePerm (pi pi' : int list) = map (fun i : int => nth 0 pi i) pi'.
    
  lemma composePermCorrect pi pi' (v : vector) : size v = k => isPerm pi => isPerm pi' =>
  permVector (permVector v pi) pi' = permVector v (composePerm pi pi').
  proof.
  move => @/isPerm @/isPerm_n sv h h'. apply eq_vectorP. split. smt(@List @M). move => i hi @/permVector.
    rewrite permVectorSize in hi. trivial. rewrite !(get_oflist zeror). smt(@List). smt(@List). rewrite !(nth_map 0).
    smt(@List @M). smt(@List @M). simplify. rewrite oflistK. rewrite nth_range. smt(@List @M permVectorSize). simplify.
    rewrite !(nth_map 0). smt(@List @Perms).
    smt(@List). simplify. rewrite nth_range.  smt(@List). rewrite size_range. smt(@List).
    rewrite nth_range. smt(@List). smt(@List).
    simplify. rewrite nth_tolist. rewrite nth_range. smt(@List).
    smt(@List). rewrite nth_range. smt(@List).   rewrite nth_range. rewrite nth_range.  smt(@List).
    simplify. rewrite sv. have : k = size pi. smt(@List). move => g. rewrite g.
    apply (perm_eq_nth _ (size pi)). smt(@List). smt(@List). smt(@List).
  qed.
  
  lemma composePermA pi pi' pi'' : isPerm pi => isPerm pi' => isPerm pi'' =>
    composePerm (composePerm pi pi') pi'' =
    composePerm pi (composePerm pi' pi'').
  proof.
    move => @/isPerm @/isPerm_n h h' h''. apply (eq_from_nth 0). rewrite !size_map. trivial.  move => i hi. rewrite !(nth_map 0).
    smt(@List). smt(@List). smt(@List). simplify. rewrite !(nth_map 0). clear h.
    have : size pi' = size pi''. smt(@List). move => g. rewrite g. apply (perm_eq_nth _ (size pi'')).
    smt(gt0_k @List). smt(@List). smt(@List).
  qed. 

  lemma composePermNeg pi : isPerm pi =>
    composePerm pi (invPerm pi) = permID /\
    composePerm (invPerm pi) pi = permID.
  proof.
    move => @/isPerm @/isPerm_n h. split. apply (eq_from_nth 0). smt(@List). move => i hi. rewrite (nth_map 0). smt(@List).
    rewrite (nth_map 0).
    smt(@List). simplify. rewrite nth_index. smt(@List). smt(@List). apply (eq_from_nth 0). smt(@List). move => i hi.
    rewrite (nth_map 0). smt(@List). simplify. rewrite (nth_map 0). smt(@List). simplify. rewrite nth_range. smt(@List). simplify.
    rewrite index_uniq. smt(@List). smt(@List). smt(@List).
  qed.

  lemma  composePermID pi : isPerm pi =>
    composePerm pi permID = pi /\
    composePerm permID pi = pi.
  proof.
    move => h. split. apply (eq_from_nth 0). smt(@List). move => i hi. rewrite (nth_map 0). smt(@List). smt(@List).
    apply (eq_from_nth 0). smt(@List). move => i hi. rewrite (nth_map 0). smt(@List). simplify.
    rewrite nth_range. simplify. have : size pi = k. smt(@List). move => g. rewrite -g.
    apply (perm_eq_nth _ (size pi)). smt(@List). smt(@List). trivial.
  qed.

  lemma mu1Perm pi pi' : isPerm pi => isPerm pi' =>
    mu1 (duniform (allperms (range 0 k))) pi =
      mu1 (duniform (allperms (range 0 k))) pi'.
  proof.    
    move => isPerm isPerm'. apply duniform_uni; apply isPermSimp2; trivial.
  qed.

  lemma gt0_fact : forall n, 0 < fact n.
  proof.
    apply natind => n ge0_n. simplify. smt(@Binomial). move => hyp. smt(@Binomial).
  qed.
      
  lemma permNotEmpty : allperms (range 0 k) <> [].
      have : 0 < size (allperms (range 0 k)). rewrite size_allperms_uniq_r. smt(@List). smt(@List). apply gt0_fact.
      move => h. smt(@List).
  qed.

  lemma composePermPerm pi pi' : isPerm pi => isPerm pi' =>
    isPerm (composePerm pi pi').
  proof.
  move => @/isPerm h h' @/isPerm_n @/composePerm. rewrite (perm_eq_trans pi).
    apply (perm_eq_sub 0 k pi' pi).
    smt(gt0_k @List). smt(gt0_k @List).  smt(gt0_k @List). 
  qed. 

  lemma weightPerm (v : vector) pi : isPerm pi => size v = k => weight v = weight (permVector v pi). 
      move => h h' @/weight.
      apply perm_eqP. apply perm_eq_permVector; trivial. 
  qed. 
    
  
  lemma checkWPerm (v : vector) pi : isPerm pi => size v = k => checkW v = checkW (permVector v pi). 
      move => h h'. move => @/checkW @/weight. smt(weightPerm).
  qed. 
    
  lemma permVectorInv : forall v pi, isPerm pi => Vectors.size v = size pi =>
      permVector (permVector v pi) (invPerm pi) = v.
  proof.
    move => @/permVector @/invPerm @/invPerm_n @/isPerm. progress. apply eq_vectorP. rewrite size_oflist. rewrite size_map. split.
    (* prove size *)
    rewrite size_range. apply perm_eq_size in H. smt(@List).
    (* eliments size *)
    move => i h. rewrite oflistK. rewrite (get_oflist ZR.zeror). smt(@List @Int). rewrite (nth_map 0). trivial. simplify.
    rewrite nth_range. smt(@List @Int). simplify. rewrite (nth_map 0 _ _ i). smt(@List @Int). simplify. rewrite nth_range. rewrite size_range in h. 
    smt(@List @Int). (* -- we have completed the easy bit *)
    have : 0 <= index i pi && index i pi < k. split. smt(@List @Int). move => h'''. have : k = size pi. smt(@List).
    move => g. rewrite g. apply has_find. have : forall l, has ((=) i) l = mem l i. smt(@List @Int). move => g'.
    smt(@List). move => g. rewrite (nth_map 0).
    (* Starting with card *) smt(@List @Int).
    (* moving to eq  *) simplify. rewrite nth_range. smt(@List).
    have : forall w v i j, i = j => 0 <= i < Vectors.size v => nth w (tolist v) i = v.[j]. smt(@Vectors).
    move => h''. apply h''. smt(@List @Int). smt(@List @Int).
  qed.

  lemma permVectorInv2 : forall v pi, isPerm pi => Vectors.size v = size pi =>
    permVector (permVector v (invPerm pi)) pi = v.
  proof.
    move => @/permVector @/invPerm @/invPerm_n @/isPerm @/isPerm_n. progress. apply eq_vectorP. rewrite size_oflist. rewrite size_map. split.
    (* prove size *)
    rewrite size_range. apply perm_eq_size in H. smt(@List).
    (* eliments size *)
    move => i h. rewrite oflistK. rewrite (get_oflist ZR.zeror). smt(@List @Int). rewrite (nth_map 0). trivial. simplify.
    rewrite nth_range. smt(@List @Int). simplify. rewrite (nth_map 0). rewrite size_range.
    rewrite size_map. rewrite size_range. smt(@List). 
    simplify. rewrite nth_range.
    smt(@List @Int). rewrite (nth_map 0 _ _ (0 + nth 0 pi i)). smt(@List). simplify. rewrite nth_range. smt(@List).
    simplify. have : index (nth 0 pi i) pi = i. smt(@List). move => h'. rewrite h'. 
    have : forall w v i j, i = j => 0 <= i < Vectors.size v => nth w (tolist v) i = v.[j]. smt(@Vectors).
    move => h''. apply h''. smt(@List @Int). smt(@List @Int).
  qed.

  lemma findPermInv v v' : arePermEq v v' =>
    permVector v' (findPermEq v v') = permVector v' (invPerm (findPermEq v' v)).
  proof.
    move => h. rewrite -findPermCorr; trivial. pose x := (invPerm (findPermEq v' v)). rewrite (findPermCorr v' v).
    (* Annoying proof Goal *)
    have : arePermEq v v'. smt(). move => h'.  elim h => pi h. exists (invPerm pi). elim h => h h''. rewrite h''.
    split. smt(@List). split. apply invPermPerm. smt(). rewrite permVectorInv. smt(). have : size v' =k. rewrite -h.
    rewrite h''. rewrite permVectorSize. smt(). trivial.
    smt(isPerm_size_k). trivial.
    (* resuming main *)
  move => @/x. rewrite permVectorInv. apply findPermChecks. elim h. move => pi h. elim h => h [h' h'']. 
    rewrite findPermSize. rewrite h''. rewrite permVectorSize; trivial. trivial.
  qed.

  lemma permVectorNth v pi i : isPerm pi => size pi = size%Vectors v =>  0 <= i < k => (permVector v pi).[i] = v.[nth 0 pi i].
  proof.
    move => @/isPerm @/isPerm_n g h y. rewrite get_offunv. smt(@List). rewrite (nth_map 0). smt(@List). simplify. rewrite nth_range. smt(@List). simplify. rewrite nth_tolist. smt(@List). trivial.
  qed.
  
  lemma permVectorAdd v v' pi : isPerm pi => size pi = size%Vectors v => size pi = size%Vectors v' =>
    permVector v pi + permVector v' pi = permVector (v+v') pi.
  proof.
    move => @/isPerm @/isPerm_n p g y. apply eq_vectorP. split. smt(@MLWE.M @Perms @List). move => i h. rewrite get_addv.
    have : size (permVector v pi + permVector v' pi) = k. rewrite size_addv. rewrite !size_oflist. smt(@List @Perms gt0_k).
    move => t. rewrite !permVectorNth; auto. smt(). smt(). rewrite size_addv. smt(@List). smt(). rewrite get_addv. trivial.
  qed.

  lemma permVectorOp v pi : isPerm pi => - permVector v pi =  permVector (-v) pi.
  proof.
    move => @/isPerm @/isPerm_n h. apply eq_vectorP. split. smt(@MLWE.M @Perms @List). move => i h''. move => @/permVector.
    rewrite (get_oflist ZR.zeror).
    smt(@MLWE.M @Perms @List). rewrite getvN.  rewrite (get_oflist ZR.zeror). smt(@MLWE.M @Perms @List).
    rewrite (nth_map 0). smt(@MLWE.M @Perms @List). rewrite (nth_map 0). smt(@MLWE.M @Perms @List). simplify.
    case (0 <= nth 0 pi (nth 0 (range 0 k) i) && nth 0 pi (nth 0 (range 0 k) i) < size v). move => h'''.
    rewrite nth_tolist. smt(@List).  rewrite nth_tolist. smt(@List). smt(@MLWE.M). trivial. move => j. rewrite andabP in j.
    rewrite negb_and in j. elim j; move => j. have :  0 <= nth 0 pi (nth 0 (range 0 k) i). rewrite nth_range.
    smt(@List permVectorSize  @MLWE). smt(@List). move => j'. smt(). elim h'' => h' h''. rewrite size_oppv in h''.
    rewrite permVectorSize in h''. smt(@List). rewrite nth_range. smt(@List). smt(@MLWE.M @List).
  qed.

  (* Defining images for the libaries *)

  (* inImage of a matrix m for a vector means there exists a vector v' which results in v when multiplies with m *)
  op isImage m (v v' : vector) = size v' = cols m /\ m *^ v' = v.
  op inImage (m : matrix)(v : vector) = exists v', isImage m v v'.

  (* the image returns the v' from v if v' exists otherwise return some default value *)
  op image (m : matrix)(v : vector) : vector = choiceb (isImage m v) (zerov (cols m)).

  lemma inImageDr m v v' : inImage m v /\ inImage m v' => inImage m (v+v').
  proof.
    move => h. (* Case 1 *) elim h => h h'. elim h => y h. elim h' => y' h'. exists (y + y'). split. smt(@M). rewrite mulmxvDr.
    elim h => h g. elim h' => h' g'. smt(@MLWE.M). 
  qed.
  
  lemma inImageSize x y : size (image x y) = cols x.
  proof.
    case(exists v', isImage x y v') => h. smt (choicebP). move => @/image. rewrite choiceb_dfl. smt().
    smt(@List).
  qed.

  lemma catv_subvC_gen v i j : j = size%Vectors v => 0  <= i <= size v => 
      (subv v 0 i || subv v i j) = v.
      proof.
        smt(@MLWE.M).
    qed.
    
  lemma subv_catvCr_inin v1 v2 : v1 \in dvector dR l => v2 \in dvector dR v =>
      subv (v1 || v2) l (l + v) = v2.
  proof.
    smt(@MLWE.M gt0_l gt0_v).    
  qed.
  
  lemma subv_catvCr_ss v1 v2 : size%Vectors v1 = l => size%Vectors v2 = v =>
      subv (v1 || v2) l (l + v) = v2.
  proof.
    smt(@MLWE.M gt0_l gt0_v).
  qed.
  
  lemma subv_catvCr_ins v1 v2 : v1 \in dvector dR l => size%Vectors v2 = v =>
      subv (v1 || v2) l (l + v) = v2.
  proof.
    smt(@MLWE.M gt0_l gt0_v).
  qed.

    
lemma probSimp (p : 'a -> bool)(k : 'a distr) : p = predT => mu k p = mu k predT.
    auto.
qed.

(* Useful lemmas - for latter proofs *)
lemma pi_c_m_size (pi : int list) (f c m r : vector) (M : matrix) :
  size c = rows M /\ rows M = k /\ size m = l /\ size r = v =>
  pi \in duniform (allperms (range 0 k)) =>
  f \in dvector dR k =>
  size pi = max (size f) (size (c - M *^ (m|| r))).
proof.
  move => h h' h''. have : size f = k. smt(@MLWE.M). have : size pi = k. apply isPerm_size_k. apply isPermSimp. trivial.
  move => g g'. smt(@MLWE.M). 
qed.

lemma f_c_m_size (f c m r : vector) (M : matrix) :
  size c = rows M /\ rows M = k /\ size m = l /\ size r = v =>
  f \in dvector dR k =>
  size f = size (c - M *^ (m|| r)).
proof.
  move => h h'.  have : size f = k. smt(@MLWE.M). move => g. smt(@MLWE.M). 
qed.

lemma bRing_cancel_sub (f a b : vector) : size f = size a => a=b =>
    f = f + a + b.
proof.
 move => h0 h. rewrite -(bRing b). subst. rewrite -addvA. rewrite addvN. smt(@MLWE.M).
qed.    

lemma bRing_cancel (f a : vector) : size f = size a =>
    f = f + a + a.
proof.
  move => h. apply bRing_cancel_sub; trivial.
qed.    
