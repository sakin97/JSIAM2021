require import AllCore DBool List Int.
require import Distr.

(* The type of plaintexts: bitstrings of length k, l *)
type block.
type result, cap.
type state = (result * cap).
type msg.

op uMsg: (msg * msg) distr.

const IV1: result.
const IV2: cap.

const IV = (IV1, IV2).
 
const z0: block.

module type Adversary = {
  proc choose(): msg * msg 
}.


(** 圧縮関数 **)
op f : block -> state -> state.
op g : block -> state -> state.

(* GMDの繰り返し部分 *)
op gstar : block list -> state -> state.

axiom gstar_nil:
  forall (y: state), gstar [] y = y.

axiom gstar_last:
  forall (x: block, y: state), (gstar (x::[]) y) = gstar [] (g x y).

axiom gstar_cons:
  forall (x: block, y: state, xs: block list),
    xs <> [] => gstar (x::xs) y = gstar xs (f x y).

(* suffix-free padding *)
op pad : msg -> block list.

axiom suffix_free:
  forall (m, m': msg, bl: block list), m <> m' => pad m <> bl ++ pad m'.

(* GMDの定義 *)
op GMD(m: msg) = fst(gstar (pad m) IV).

(* fの衝突ペアかどうかを評価する関数*)
op coll(xy, xy': block * state) =
  xy <> xy' && f (fst xy) (snd xy) = f (fst xy') (snd xy').

(* gの衝突ペアかどうかを評価する関数*)
op coll_last(xy, xy': block * state) = 
  xy <> xy' && fst (g (fst xy) (snd xy)) = fst (g (fst xy') (snd xy')).

(* リストについての補助定理 *)
lemma size_behead : forall (xs: 'a list),
  0 < size xs => size(behead xs) < size xs.
smt(). qed.

(** 
    GMD全体のCollision Finder
    攻撃者Aが選んだ平文m1, m2がGMDの衝突を引き起こせばtrueを返す
 **)
module CR_GMD(A: Adversary) = {
  (* 与えられた平文mからGMD(m)を計算するアルゴリズム *)
  proc oracle(m: msg) : result = {
    var xs: block list <- pad m;
    var y : state <- IV;
    while (xs <> []) {
      if ( size xs = 1 ) {
        y <- g (head z0 xs) y;
      } else {
        y <- f (head z0 xs) y;
      }
      xs <- behead xs;
    }
    return fst y;
  }

  (* Collision Finder本体*)
  proc main() : bool = {
    var m1, m2 : msg;
    var h1, h2 : result;
    (m1, m2) <@ A.choose();
    h1 <@ oracle(m1);
    h2 <@ oracle(m2);
    return (m1 <> m2 && h1 = h2);
  }
}.

(**
    圧縮関数のCollision Finder
    攻撃者Aが選んだ平文m1, m2から圧縮関数f,g'=chop \circ gの衝突ペアを
    発見できればtrueを返す
**)
module CR_comp(A: Adversary) = {
  proc adv_b() : bool = { 
    var m1, m2 : msg;
    var y1, y2 : state;
    var xs', xs1, xs2 : block list;
    var flag: bool <- false;

    (m1, m2) <@ A.choose();
    (* xs1, xs2: m1,m2をpaddingした結果 *)
    xs1 <- pad m1; y1 <- IV;
    xs2 <- pad m2; y2 <- IV;
    xs' <- [];

    (** 
      xs1とxs2の長さを合わせる: 
      長い方の先頭からGMDのアルゴリズムに沿ってfとgを適用する
    **)
    while (size xs2 < size xs1) {
      if (size xs1 = 1) {
        y1 <- g (head z0 xs1) y1;
      } else {
        y1 <- f(head z0 xs1) y1;
      }

      xs' <- xs' ++ [head z0 xs1];
      xs1 <- behead xs1;
    }

    while (size xs1 < size xs2) {
      if (size xs2 = 1) {
        y2 <- g (head z0 xs2) y2;
      } else {
        y2 <- f (head z0 xs2) y2;
      }
      xs' <- xs' ++ [head z0 xs2];
      xs2 <- behead xs2;
    }

    (* 
        Collision Finderの本体部分:
        xs1, xs2の先頭から順にGMDのアルゴリズムに沿ってf,gを適用し、
        fまたはg'の衝突ペアが見つかるか、xs1とxs2を最後まで調べきったら停止
    *)
    while (
      (1 < size xs1 => ! (coll((head z0 xs1), y1) ((head z0 xs2), y2))) && 
      (size xs1 <= 1 => !(coll_last((head z0 xs1), y1) ((head z0 xs2), y2))) &&
        0 <> size xs1) {
      if ( size xs1 = 1 ) {
        y1 <- g (head z0 xs1) y1; xs1 <- behead xs1;
        y2 <- g (head z0 xs2) y2; xs2 <- behead xs2;
      } else {
        y1 <- f (head z0 xs1) y1; xs1 <- behead xs1;
        y2 <- f (head z0 xs2) y2; xs2 <- behead xs2;
      }
    }

    (* 本体部分停止時点でfまたはg'の衝突ペアが見つかっていたらtrueを返す *)
    return coll ((head z0 xs1), y1) ((head z0 xs2), y2)
      \/ coll_last((head z0 xs1), y1) ((head z0 xs2), y2);
  }

  proc main(): bool = {
    var xy1, xy2: block * state;
    var flag: bool;
    flag <@ adv_b();
    return flag;
  }
}.

prover["Alt-Ergo"].

section Security.
declare module Adv: Adversary.
lemma GMD_Collision_Resistance &m :
    Pr[CR_GMD(Adv).main() @ &m : res] <= Pr[CR_comp(Adv).main() @ &m : res].
    proof. 

    (* 
      確率の式を以下のpRHLの論理式に変換 
    *)
    byequiv=>//.
    proc.
    
    (* CR_GMDとCR_compで同じm1, m2を使っていることを示す *)
    inline CR_comp(Adv).adv_b. sp. seq 1 1 : (={m1, m2}). sim.

    (*
       CR_GMD.oracleがGMDを正しく実装していることを示す。
       {1}(CR_GMD)側の手続きが取り除かれ、
       事前条件に(h1{1} = GMD m1{1} && h2{1} = GMD m2{1})が追加され、
       事後条件がm1{1} <> m2{1} && h1{1} = h2{1} => flag{2}となる
    *)
    seq 1 0 : ((h1 = GMD m1){1} && ={m1, m2}).
    inline *; sp. wp.
    while{1} (fst(gstar xs y) = GMD m1){1} (size xs{1}).
    auto. smt. 
    skip. progress. by progress; smt. smt.
    seq 1 0 : ((h1 = GMD m1 && h2 = GMD m2){1} && ={m1, m2}).
    inline*. sp. wp.
    while{1} (fst(gstar xs y) = GMD m2){1} (size xs{1}).
    auto. progress.
    smt. smt. smt. smt().
    skip. by progress; smt.
    
(* 
圧縮関数のCollisionFinder(CR_comp)で衝突が見つかること、すなわち、
CR_compの手続きをうまく事前条件と事後条件に取り除いて、
事後条件で

m1{1} <> m2{1} && h1{1} = h2{1} => flag{2}

が成り立つことを示す。

m1, m2はCR_GMD({1})と同じものを使えるので、
CR_comp実行後に、
(m1 <> m2 && GMD m1 = GMD m2) => fまたはg'の衝突ペアを発見
を示せばよい
*)
sp.
wp.
(* m1 = m2のときはtrivial *)
case (m1{2} = m2{2}).
while{2} true (size xs1{2}). 
progress. wp. skip. by progress; smt.
rcondf{2} 1 => //.
rcondf{2} 1 => //.
skip. progress. smt.

(* m1 <> m2 && size xs1 <= size xs2のとき *)
case (size xs1{2} <= size xs2{2}).

rcondf{2} 1. auto.  smt.
    
(* 
  CollisionFinderの本体部分を取り除く。
  以降の証明に必要なloop invariantを与える
*)
while{2} (
  fst(gstar xs1 y1) = GMD m1 && (* CollisionFinderで計算している途中経過が正しくGMDの計算経過になっている *)
  fst(gstar xs2 y2) = GMD m2 &&
  size xs1 = size xs2 && (* xs1とxs2の長さは常に同じ *)
  (xs1 = xs2 => ((fst y1 <> fst y2) \/ (y1 <> y2))) &&
  (size xs1 = 0 => fst y1 <> fst y2)
    ){2} (size xs1){2}.
auto. simplify. progress.
(* whileタクティックの規則によってsize xs1 = 0の場合は除かれる *)
(* size xs1 = 1 のとき *)
smt(@List gstar_last size_behead).
smt(@List gstar_last size_behead). smt(). 
smt().
smt(@List).
smt().
(* 1 < size xs1 のとき *)
smt(gstar_cons). smt(gstar_cons). smt(). smt(size_ge0).
(* size xs1 <> 1 のとき 仮定で size (behead xs1) = 0 を導けるのでtrivial *)
have: (size xs1{hr} <> 1 && size xs1{hr} = 1). smt(). trivial.
apply size_behead. smt(size_ge0).

    
(* 長さ調整部分を取り除く *)
while{2} (
  xs' ++ xs2 = pad m2 &&
  (fst(gstar xs2 y2) = GMD m2) &&
  size xs1 <= size xs2
){2}
    (size xs2 - size xs1){2}.
auto. move => &hr. case. case. case. move => pad_m2 ? ? ?. 
split.
move => ?. simplify.
split. split. rewrite -pad_m2. smt(@List). move => ?. split.
smt(size_ge0 gstar_last). 
move => ?. smt(size_behead). smt(size_behead).
    move => ?. simplify. split. split. smt(@List).
    move => ?. split. smt(@List gstar_cons). move => ?. smt(). smt(size_ge0).

    
(* 手続きをすべて取り除いたので、一階述語論理式に変換して証明を行う *)
skip. progress. smt(). smt(). right. smt(suffix_free). smt(size_eq0 suffix_free).
    case (size xs1_R <> 0). smt(size_ge0). 
    have: (xs1_R = []). smt(size_ge0). move => ->>. simplify. trivial.
    (* xs1_R <> 0のとき: 仮定を使って、現在着目しているペアで衝突していることを示す *)
    case (size xs1_R = 1). move => ?. have pair_coll_last: (coll_last (head z0 xs1_R, y1_R) (head z0 xs2_R0, y2_R0)). smt(). rewrite pair_coll_last; trivial.
    move => size_xs1_R_neq_1.
    case: (1 < size xs1_R ). move => size_xs1_R_gt_1. have pair_coll: (coll (head z0 xs1_R, y1_R) (head z0 xs2_R0, y2_R0)). smt(). rewrite pair_coll; trivial.
    
    (* xs1_Rが0のとき: 仮定から前件がfalseな論理包含を作って示す
       これを示すために loop invariantにsize xs1 = 0 => fst y1 <> fst y2を導入した *)
    move => size_xs1_R_lt_1. have: (size xs1_R = 0). smt(@List). 
    move => size_xs_R_eq_0. have: (xs1_R = []). smt(size_eq0). have: (xs2_R0 = []). smt(size_eq0). move => ->> ->>. right.  rewrite /coll_last. simplify. split. smt().
rewrite gstar_nil in H7. rewrite gstar_nil in H6. move => H13. 
move: H5 => _. congr. congr.
have H10': (y1_R.`1 <> y2_R0.`1). progress. move: H10 => _. move: H9 => _.
move: H8 => _. have H12': (y1_R.`1 = y2_R0.`1). smt().
have: ( y1_R.`1 <> y2_R0.`1 && y1_R.`1 = y2_R0.`1). progress. trivial.

(* m1 <> m2 /\ size xs2 < size xs1 のときも同様の方法で示す *)
  wp.
  while{2} (
      fst(gstar xs1 y1) = GMD m1 && 
      fst(gstar xs2 y2) = GMD m2 && 
      size xs1 = size xs2 &&
      (xs1 = xs2 => ((fst y1 <> fst y2) \/ (y1 <> y2) )) &&
      (size xs1 = 0 => fst y1 <> fst y2)
){2} (size xs1){2}. 

auto. smt.
rcondf{2} 2. progress. 
while (
    (fst (gstar xs1 y1) = GMD m1) &&
    xs' ++ xs1 = pad m1 &&
    size xs2 <= size xs1
).
if. wp. skip. progress. smt(@List gstar_last gstar_cons gstar_nil).
smt(@List). smt().
wp. skip. progress.
smt. smt(@List). smt().
skip. progress. smt(). smt(). 
while{2} (
   fst (gstar xs1 y1) = GMD m1 &&
    xs' ++ xs1 = pad m1 &&
    size xs2 <= size xs1){2} (size xs1){2}.
progress. wp. skip.
progress. smt(@List gstar_cons gstar_last). smt(@List).
smt(). smt().
    smt(@List gstar_cons). smt(@List). smt(). smt(size_eq0 size_ge0 size_behead).
skip. progress. smt(). smt. smt(). smt(suffix_free). smt(size_eq0 suffix_free).
smt(size_ge0).  smt.
qed.
