/- # mvcgen を使って命令的プログラムの検証をする

> この記事は Sebastian Graf さんによる記事
> [Verifying imperative programs using mvcgen](https://hackmd.io/@sg-fro/BJRlurP_xg) の非公式日本語訳です。

`mvcgen` タクティックはモナディックな検証条件生成器 (monadic verification condition generator) を実装しています。
このタクティックは Lean の命令的な `do` 記法で書かれたプログラムを含むゴールを、純粋な検証条件の集合に分解して処理します。
ここでいう検証条件 (verification condition) とは、`do` ブロックの背後にあるモナドを一切参照しない部分ゴールのことです。
つまり、プログラムの命令的な部分を抽象化し、最終的にモナドに依存しない純粋な性質を証明すれば、もとのゴール全体も成立する、という仕組みです。

mvcgen への「Hello world」として、次の例では `mySum` がローカルな可変変数と `for` ループを使って配列の総和を計算します。
そのうえで、この `mySum` が `Array.sum` と同値であることを証明します。
その際には、ループに対して不変条件 (invariant) を明示的に指定する必要があります。
-/
import Std.Tactic.Do
import Lean

-- mvcgen はまだ使用しないでというwarningを消す
set_option mvcgen.warning false

/-- for文を使ってリストの和を計算する -/
def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

open Std.Do

theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- モナディックに実装されている（`Id.run do ...`）部分にフォーカスします
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- 検証条件に分解する
  mvcgen
  -- ループ全体を通して成り立たせたい不変条件を指定する
  -- * `out` は `let mut` で導入した変数の現在値を表します
  -- * `xs` は `List.Cursor` で，リストを接頭辞 `xs.prefix` と接尾辞 `xs.suffix` に
  --   分割して表すデータ構造です。どこまでループが進んだかを追跡します。
  --   つまり進捗（ループの到達位置）を記録します。
  -- 不変条件は「`out` が接頭辞の総和を保持している」ことです。
  -- 記法 ⌜p⌝ は，純粋な命題 `p : Prop` をアサーション言語に埋め込みます。
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- 不変条件を指定した後は，“証明モードを抜ける”ことでゴールをさらに簡約できます。
  -- `mleave` は安定した `simp` サブセットに対する `simp only [...] at *` の糖衣です。
  all_goals mleave
  -- 各反復で不変条件が保存されることを証明する
  case vc1.step ih =>
    -- ここでのゴールには `pref` が現れます。これは不変条件に渡されたカーソルの
    -- `prefix` フィールドを束縛したものです。依存型のカーソルを展開すると
    -- `grind` が働きやすくなります。
    grind
  -- ループ開始時に不変条件が成り立つことを証明する
  case vc2.a.pre =>
    grind
  -- ループ終了時の不変条件から目標の性質が従うことを証明する
  case vc3.a.post h =>
    grind

/-
ループ不変条件を指定したあとは、証明は `all_goals mleave; grind` だけにまで短縮できます。
なお、`case` ラベルには `vc1`、`vc2`、`vc3` などの一意なプレフィックスが付きます。
ケースを参照するときは、このプレフィックスだけを使うべきで、サフィックスはその検証条件（VC）がどこから来たかをユーザーに伝えるための簡易な手掛かりに過ぎません。

例えば:

* **`vc1.step`** は、この検証条件がループにおける帰納ステップ（不変条件が次の繰り返しでも保持されること）を証明するものであることを示しています。
* **`vc2.a.pre1`** は、与えられたゴールの仮定が `forIn` の仕様における事前条件を満たすことを証明するものです。
* **`vc3.a.post`** は、`forIn` の仕様における事後条件からゴールが目標とする性質が導かれることを証明するものです。

`mvcgen`を使用しない伝統的な正しさ証明（correctness proof）と比較してみると役に立ちます。
-/

theorem mySum_correct_traditional (l : Array Nat) : mySum l = l.sum := by
  -- 配列をリストに変換する
  cases l with | mk l =>
  -- `mySum` を展開し，`forIn` を `foldl` に書き換える
  simp [mySum]
  -- 帰納法の仮定を一般化する
  suffices h : ∀ out, List.foldl (· + ·) out l = out + l.sum by simp [h]
  -- grind で片づける
  induction l with grind

/-
この証明は、`mvcgen` を用いた証明と同様に簡潔です。
しかし、従来型の手法はプログラムの重要な性質に依存しています：

* `for` ループが途中で `break` したり早期に `return` したりしないこと。そうでないと、`forIn` を `foldl` に書き換えることはできません。
* ループ本体 `(· + ·)` が、証明の中で繰り返し展開しても扱える程度に小さいこと。
* ループ本体が純粋 (pure) であり、すなわち副作用 (effects) を伴わないこと。
  （実際、基底モナド `Id` の計算はすべて `pure` を介して表せます。）

`forIn` は `foldlM` へ書き換えること自体は可能ですが、モナディックなループ本体について推論するのは `grind` にとって骨が折れる場合があります。

以下のセクションでは、`mvcgen` とそのサポートライブラリを学ぶためにいくつかの例を順に見ていき、あわせて従来型の証明が難しくなる場面も確認します。これはたいてい次の理由で生じます。

* 早期 `return` を伴う（ネストした）`for` ループなどの制御フロー構文を用いる `do` ブロック。
* `Id` 以外のモナドにおける効果的（effectful）な計算。そのような計算は暗黙のモナディック文脈（状態・例外など）に影響を与え，その影響をループ不変条件に反映する必要がある。

`mvcgen` は、これらの課題に対しても合理的な労力でスケールします。
-/

/-
## control flow

for ループと早期 `return` を組み合わせた別の例を考えてみましょう。
`List.Nodup` は、与えられたリストが重複を含まないことを主張する述語であることを思い出してください。
以下の例の関数 `nodup` は、この述語を判定します。
-/

/-- リストに重複がないか判定する。
true なら重複がない。false なら重複がある。-/
def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 =>
    exact Invariant.withEarlyReturn
      -- 早期リターンしたとき
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      -- 通常の帰納ステップ
      (onContinue := fun xs seen => ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
  all_goals mleave; grind

/-
最初の `mySum` 例と同様に、この証明も簡潔な構造を保っています。というのも、今回も `grind` と、`List.Nodup` をめぐる既存の枠組みに証明の大半を委ねているからです。
したがって、違いは不変条件にあるだけです。
ループに早期 `return` があるため、補助関数 `Invariant.withEarlyReturn` を使って不変条件を構成します。
この関数によって、不変条件を次の三つの部分に分けて指定できます。

* `onReturn ret seen` は、ループが値 `ret` を伴う早期 `return` によって抜けた後に成り立つべき性質です。
  `nodup` の場合、返される唯一の値は `false` であり、そのとき `nodup` はリストに重複があると判定したことになります。

* `onContinue xs seen` は、各反復で不変条件が保存されることを示す通常の帰納ステップです。
  反復の状態はカーソル `xs` によって表現されます。
  与えられた例では、集合 `seen` がこれまでのループ反復で現れたすべての要素を含み、かつこれまで重複がなかったことを主張します。


`onExcept` は、ループが例外を投げたときに成り立つべき性質です。
`Id` には例外がないため、ここは指定せずデフォルトを用います。
（例外については後で議論します。）

では、`mvcgen` を使わない直接的（かつ過度にゴルフされた）証明を次に示します：
-/

theorem nodup_correct_directly (l : List Int) : nodup l ↔ l.Nodup := by
  rw [nodup]
  generalize hseen : (∅ : Std.HashSet Int) = seen
  change ?lhs ↔ l.Nodup
  suffices h : ?lhs ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen by grind
  clear hseen
  induction l generalizing seen with grind [Id.run_pure, Id.run_bind]

/-
いくつか所見が得られます：

* この証明は、`mvcgen` を用いたものよりさらに短い。
* `generalize` を使ってアキュムレータを一般化する方法は、一般化の対象となる `∅` の出現箇所がちょうど1つであることに依存している。
  もしそうでなければ、証明の中にプログラムの一部を持ち込まざるを得ず、これは大きな関数に対しては現実的ではない。
* 適切な補題が与えられていれば、`grind` は関数の制御フローに沿って分割し、`Id` について推論してくれる。
  これは `Id.run_pure` や `Id.run_bind` には効くが、たとえば `Id.run_seq` には効かない。
  というのも、その補題は E-matchable ではないからだ。
  `grind` が失敗する場合は、`grind` が再び拾えるところまで、制御フローの分割やモナディックな推論をすべて手作業で行わざるを得ない。

証明対象の定義の制御フローを複製せずに済ませる通常の方法は、`fun_cases` や `fun_induction` タクティクを用いることです。
しかし残念ながら、例えば `forIn` の適用内部にある制御フローについては、`fun_cases` は助けになりません。

これは mvcgen と対照的です。mvcgen には多くの `forIn` 実装のサポートが同梱されており、カスタムの `forIn` 実装についても `@[spec]` アノテーションを付けるだけで容易に拡張できます。
さらに、mvcgen による証明では、元のプログラムの一部をコピーしなければならない状況は決して発生しません。
-/

/-
## Hoare 三つ組を用いた副作用を持つプログラムに対する合成的推論

これまでの例では、`Id.run do <prog>` を使って定義された関数について推論し、`<prog>` 内でのローカルな可変性や早期リターンを利用してきた。
しかし、実際のプログラムでは、状態や失敗条件を暗黙の「効果」として隠蔽するために、しばしば `do` 記法とモナド `M` が使われる。
この場合、関数は通常 `M.run` を省略し、代わりにモナディックな戻り値型 `M α` を持ち、その型を持つ他の関数とよく合成できるようになっている。

以下は、自動インクリメントのカウンタ値を返す状態付き関数 `mkFresh` を用いた例です。
-/

structure Supply where
  counter : Nat

def mkFresh : StateM Supply Nat := do
  let n ← (·.counter) <$> get
  modify (fun s => {s with counter := s.counter + 1})
  pure n

def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList

/-
`mkFreshN n` は、`mkFresh` を通じて内部の Supply 状態を変更しながら、n 個の「新しい」数を返します。
ここで「新しい」とは、これまでに生成された数のすべてが、次に生成される数と異なることを意味します。
この正しさの性質を、`List.Nodup` を用いて `mkFreshN_correct` として定式化し、証明することができます。
-/

theorem mkFreshN_correct {s : Supply} (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  -- `(mkFreshN n).run' s` に注目する
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  -- モナディックなプログラム `mkFresh n` について述べる
  -- `mvcgen` への `mkFreshN` と `mkFresh` の引数は内部の `simp` 集合に追加され、
  -- `mvcgen` がこれらの定義を展開するようにする
  mvcgen [mkFreshN, mkFresh]
  -- 不変条件：カウンタは蓄積済みのあらゆる数より大きく、
  --         かつ蓄積済みの数はすべて相異なる
  -- この不変条件は引数 `state : Supply` を通じて状態を参照することができる
  -- 次に蓄積する数はカウンタであるため、蓄積済みのすべての数と異なる
  case inv1 => exact ⇓⟨xs, acc⟩ state => ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  all_goals mleave; grind

/- ### 仕様の合成

`mvcgen [mkFreshN, mkFresh]` のように定義を入れ子にして展開する方法は、かなり大ざっぱですが、小さなプログラムに対しては有効です。
より合成的な方法としては、各モナディック関数ごとに個別の仕様補題を作成することです。
これらの補題は、`mvcgen` への引数として渡すこともできますし、`@[spec]` 補題を用いて、仕様のグローバル（あるいはスコープ付き、ローカル）データベースに登録することもできます。
-/

/-- mkFresh は

1. 今のカウンタ値を返す
2. カウンタをインクリメントする
-/
@[spec]
theorem mkFresh_spec (c : Nat) : ⦃fun state => ⌜state.counter = c⌝⦄ mkFresh ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  -- `mkFresh` を展開して一気に片を付ける
  mvcgen [mkFresh]
  grind

@[spec]
theorem mkFreshN_spec (n : Nat) : ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- `mkFresh_spec` が `@[spec]` で登録されていなければ `mvcgen [mkFreshN, mkFresh_spec]` とする
  mvcgen [mkFreshN]
  -- 先と同様
  case inv1 => exact ⇓⟨xs, acc⟩ state => ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  all_goals mleave; grind

theorem mkFreshN_correct₂ {s : Supply} (n : Nat) : ((mkFreshN n).run' s).Nodup :=
  -- `mkFreshN` の型 `⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄` は
  -- `∀ (n : Nat) (s : Supply), True → ((mkFreshN n).run' s).Nodup` と定義的等価
  mkFreshN_spec n s True.intro

/-
ここでの記法 `⦃fun state => ⌜state.counter = c⌝⦄ mkFresh ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄` は、Hoare 三つ組（cf. Std.Do.Triple）を表している。
モナディック関数の仕様は、常にこのような Hoare 三つ組の結果型を持つ。
-/

/- ### Hoare 三つ組

ホーア三つ組 `⦃P⦄ prog ⦃Q⦄` は、「状態に対して前提条件 P が成り立つならば、モナディックプログラム prog を実行した後には後提条件 Q が成り立つ」という意味です。
したがって、`mkFresh` の仕様定理は次のように述べられます：

> もし `c` が `Supply` の事前状態（prestate）のカウンタフィールドを表しているなら、`mkFresh` を実行すると戻り値として `c` を返し、事後状態（poststate）のカウンタを `c` より大きい値に更新します。

この仕様は「情報を捨てている（lossy）」ことに注意してください。
`mkFresh` は状態を任意の非負の量だけ増加させても、依然としてこの仕様を満たします。
これは望ましい性質です。なぜなら、仕様は興味のない実装の詳細を抽象化できるため、堅牢で小さな証明を保つことができるからです。

ホーア三つ組は、状態付き述語の論理と、モナディックプログラムをその論理に翻訳する「最弱事前条件」意味論 `wp⟦·⟧` に基づいて定義されます。

````lean
def Triple [WP m ps] {α : Type u} (x : m α) (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦x⟧ Q
````
-/
--#--
/--
info: def Std.Do.Triple.{u, v} : {m : Type u → Type v} →
  {ps : PostShape} → [WP m ps] → {α : Type u} → m α → Assertion ps → PostCond α ps → Prop :=
fun {m} {ps} [WP m ps] {α} x P Q => P ⊢ₛ wp⟦x⟧ Q
-/
#guard_msgs in
#print Triple
--#--
/-
`WP` 型クラスはモナド `m` をその `ps : PostShape` に対応付けます。この `PostShape` が、ホーア三つ組の具体的な形を決定します。
`StateT`、`ReaderT`、`ExceptT` などの標準的なモナド変換子の多くには、標準的な（canonical）`WP` インスタンスが付属しています。

たとえば、`StateT σ` には、すべての主張（Assertion）に対して `σ` 引数を追加する `WP` インスタンスがあります。
状態付き含意 `⊢ₛ` は、これらの追加された `σ` 引数に対して η 展開されます。

`StateM` プログラムに関しては、次の型がホーア三つ組 `Triple` と定義的等価になります。
-/

def Triple' {α σ : Type u} (x : StateM σ α) (P : σ → ULift Prop) (Q : (α → σ → ULift Prop) × PUnit) : Prop :=
  ∀ s, (P s).down → let (a, s') := x.run s; (Q.1 a s').down

example : @Triple' α σ = Triple (m := StateM σ) := rfl

/-
一般的な後提条件記法 `⇓ r => ...` は、型 `α → Assertion ps` の主張を `PostCond ps` へと埋め込みます。
`StateM` の場合は、これを空のタプル `PUnit.unit` と結合して実現します。

例外が加わると、後提条件の形はさらに興味深いものになります。

記法 `⌜p⌝` は、純粋な仮定 `p : Prop` を状態付き主張（stateful assertion）へと埋め込みます。
逆に、任意の状態付き仮定 `h : Assertion ps` が、ある `p : Prop` に対して `⌜p⌝` と同値であるとき、それを「純粋（pure）」と呼びます。

純粋な状態付き仮定は、通常の Lean のコンテキストと自由に行き来させることができます。
（これを手動で行うには、`mpure` タクティックを使います。）

#### 純粋な前提条件とフレーム規則の概念に関する進んだ補足

この小節は少し脇道にそれる内容なので、初読では飛ばしてかまいません。

Aeneas に着想を得たモナディックな加算関数 `x +? y : M UInt8` の仕様が「加算がオーバーフローしない」、すなわち `h : x.toNat + y.toNat ≤ UInt8.size` を要件として課すとします。
この要件は、仕様の通常の Lean の仮定（`add_spec_hyp`）としてエンコードすべきでしょうか？ それとも、`⌜·⌝` 記法を用いて、ホーア三つ組の純粋な前提条件（`add_spec_pre`）としてエンコードすべきでしょうか？

```lean
theorem add_spec_hyp (x y : UInt8) (h : x.toNat + y.toNat ≤ UInt8.size) :
    ⦃⌜True⌝⦄ x +? y ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := sorry

theorem add_spec_pre (x y : UInt8) :
    ⦃⌜x.toNat + y.toNat ≤ UInt8.size⌝⦄ x +? y ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := sorry
```

第一のアプローチを勧めます。もっとも、実際上は差が出ないはずです。
VC 生成器（Verification Condition generator）は、純粋な仮定を状態付きコンテキストから通常の Lean のコンテキストへ移動させるため、第二の形式は事実上、第一の形式へと変換されます。
これは「仮定のフレーミング（framing hypotheses）」と呼ばれます（`mpure` および `mframe` タクティック参照）。

Lean のコンテキスト内にある仮定は、状態付き論理における不変のフレーム（immutable frame）の一部です。というのも、状態付き仮定と異なり、これらは帰結規則（rule of consequence）を適用しても保持されるからです。
-/

/- ### モナドトランスフォーマー

実際のプログラムでは、しばしば複数の独立したサブシステム間の相互作用を、モナド変換子のスタックを通じて調整します。
これを示すために、先ほどの例を少し改変してみましょう。

`mkFresh` が、任意の基底モナド `m` の上にある `StateT Supply` でも動作するように一般化されているとします。
さらに、`mkFreshN` が具体的なモナド変換子スタック `AppM` の上で定義され、`mkFresh` を `AppM` に持ち上げて使用するとします。

このとき、`mvcgen` に基づく証明は変更なしでそのまま通用します。
-/
namespace MonadTrans --#

def mkFresh [Monad m] : StateT Supply m Nat := do
  let n ← (·.counter) <$> get
  modify (fun s => {s with counter := s.counter + 1})
  pure n

abbrev AppM := StateT Bool (StateT Supply (ReaderM String))
abbrev liftCounterM : StateT Supply (ReaderM String) α → AppM α := liftM

def mkFreshN (n : Nat) : AppM (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let n ← liftCounterM mkFresh
    acc := acc.push n
  return acc.toList

@[spec]
theorem mkFresh_spec [Monad m] [WPMonad m ps] (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄ mkFresh (m := m) ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  mvcgen [mkFresh]
  grind

@[spec]
theorem mkFreshN_spec (n : Nat) : ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  mvcgen [mkFreshN, liftCounterM] -- `liftCounterM` here ensures unfolding
  case inv1 => exact ⇓⟨xs, acc⟩ _ state => ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝
  all_goals mleave; grind

end MonadTrans --#
/-
`WPMonad` 型クラスは、`wp⟦·⟧` がモナド演算に対して分配する（すなわち「モナド準同型（monad morphism）」である）ことを主張します。

この証明は、一見すると単一のモナドしか関わらない場合と大差ないように見えるかもしれません。
しかし、ユーザーの目に見えないところでは、この証明は `MonadLift` インスタンスに対する一連の仕様（specification）の連鎖の上に構築されています。
-/

/- ### 例外

mvcgen フレームワークは拡張可能に設計されています。
これまでに登場したどのモナドも、mvcgen にハードコードされているわけではありません。
そうではなく、mvcgen は `WP` および `WPMonad` 型クラスのインスタンスと、ユーザーが提供する仕様に依存して、検証条件（verification conditions）を生成します。

`WP` インスタンスは、モナド `m` を述語変換子 `PredTrans ps` へと写す「最弱事前条件（weakest precondition）」の解釈を定義します。
対応する `WPMonad` インスタンスは、この変換がモナドの各操作に対して分配する（すなわちモナド準同型として振る舞う）ことを保証します。
-/
namespace Hidden --#
/--
  A weakest precondition interpretation of a monadic program `x : m α` in terms of a
  predicate transformer `PredTrans ps α`.
  The monad `m` determines `ps : PostShape`. See the module comment for more details.
-/
class WP (m : Type u → Type v) (ps : outParam PostShape.{u}) where
  wp {α} (x : m α) : PredTrans ps α

/--
  A `WP` that is also a monad morphism, preserving `pure` and `bind`. (They all are.)
-/
class WPMonad (m : Type u → Type v) (ps : outParam PostShape.{u}) [Monad m]
  extends LawfulMonad m, WP m ps where
  wp_pure : ∀ {α} (a : α), wp (pure a) = pure a
  wp_bind : ∀ {α β} (x : m α) (f : α → m β), wp (do let a ← x; f a) = do let a ← wp x; wp (f a)

end Hidden --#
/-
たとえば、[Aeneas](https://github.com/AeneasVerif/aeneas) が生成したプログラムに対して検証条件を生成するために mvcgen を使いたいとします。
Aeneas は Rust プログラムを、次の `Result` モナドを用いた Lean プログラムへと変換します。
-/

inductive Error where
  | integerOverflow: Error
  -- ... more error kinds ...

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div

instance : Monad Result where
  pure x := .ok x
  bind x f := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

instance : LawfulMonad Result := by
  apply LawfulMonad.mk' <;> (simp only [instMonadResult]; grind)

/-
このモナドをサポートするには、次の対応を行う必要があります。

* `Result` に対する `WP` および `WPMonad` インスタンスを追加すること
* 加算など、基本的な Rust のプリミティブに対応する変換について仕様補題（specification lemmas）を登録すること

最初の部分は比較的単純です。
-/

instance Result.instWP : WP Result (.except Error .pure) where
  wp x := match x with
  | .ok v => wp (pure v : Except Error _)
  | .fail e => wp (throw e : Except Error _)
  | .div => PredTrans.const ⌜False⌝

instance Result.instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure := by intros; ext Q; simp [wp, PredTrans.pure, pure, Except.pure, Id.run]
  wp_bind x f := by
    simp only [instWP, bind]
    ext Q
    cases x <;> simp [PredTrans.bind, PredTrans.const]

theorem Result.of_wp {α} {x : Result α} (P : Result α → Prop) :
    (⊢ₛ wp⟦x⟧ post⟨fun a => ⌜P (.ok a)⌝, fun e => ⌜P (.fail e)⌝⟩) → P x := by
  intro hspec
  simp only [instWP] at hspec
  split at hspec <;> simp_all

/-
上の `WP` インスタンスは、`Result α` のプログラムを `PredTrans ps α` における述語変換子へと翻訳します。
すなわち、事後条件をその最弱事前条件へ写す、`PostCond α ps → Assertion ps` 型の関数です。
この `WP` インスタンスの定義によって、`Result.of_wp` を介して証明済みの仕様からどのような性質を導けるかが決まる点に注意してください。
この補題が、「最弱事前条件（weakest precondition）」の意味を定めます。

第2の要素を例示するために、整数オーバーフローをモデル化する `Result` における `UInt32` の加算の例を次に示します。
-/

instance : MonadExcept Error Result where
  throw e := .fail e
  tryCatch x h := match x with
  | .ok v => pure v
  | .fail e => h e
  | .div => .div

def addOp (x y : UInt32) : Result UInt32 :=
  if x.toNat + y.toNat ≥ UInt32.size then
    throw .integerOverflow
  else
    pure (x + y)

/- 登録すべき仕様補題（specification lemma）は、次の2つです。 -/

@[spec]
theorem Result.throw_spec (e : Error) :
    ⦃Q.2.1 e⦄ throw (m := Result) (α := α) e ⦃Q⦄ := id

@[spec]
theorem addOp_noOverflow_spec (x y : UInt32) (h : x.toNat + y.toNat < UInt32.size) :
    ⦃⌜True⌝⦄ addOp x y ⦃⇓ r => ⌜r = x + y ∧ (x + y).toNat = x.toNat + y.toNat⌝⦄ := by
  mvcgen [addOp] <;> simp_all; try grind

/- これだけで、次の例を証明するには十分です。-/

example :
  ⦃⌜True⌝⦄
  do let mut x ← addOp 1 3
     for _ in [:4] do
        x ← addOp x 5
     return x
  ⦃⇓ r => ⌜r.toNat = 24⌝⦄ := by
  mvcgen
  case inv1 => exact ⇓⟨xs, x⟩ => ⌜x.toNat = 4 + 5 * xs.prefix.length⌝
  all_goals simp_all [UInt32.size]; try grind

/- ## 状態を持つゴールに対する証明モード

mvcgen の優先事項のひとつは、モナディックなプログラムを人間が理解しやすい検証条件（VC）へと分解することです。
たとえば、モナドスタックが単相（monomorphic）で、すべてのループ不変式が具体化されている場合、`all_goals mleave` の呼び出しによって `Std.Do.SPred` 固有の構成要素がすべて簡約され、`grind` でも人間でも容易に理解できる目標が残るはずです。

しかし、`mleave` がすべての `Std.Do.SPred` 構成を除去できない場合もあります。
そのような場合には、`H ⊢ₛ T` のような形の検証条件が残ります（ここで `H P : Std.Do.SPred σs`）。
アサーション言語 `Assertion ps` は、このような `Std.Do.SPred σs` に次のように翻訳されます。
-/

abbrev PostShape.args : PostShape.{u} → List (Type u)
  | .pure => []
  | .arg σ s => σ :: PostShape.args s
  | .except _ s => PostShape.args s

/--
与えられた述語シェイプにおける `.arg` へのアサーションは次のようになります。

example : Assertion (.arg ρ .pure) = (ρ → ULift Prop) := rfl
example : Assertion (.except ε .pure) = ULift Prop := rfl
example : Assertion (.arg σ (.except ε .pure)) = (σ → ULift Prop) := rfl
example : Assertion (.except ε (.arg σ .pure)) = (σ → ULift Prop) := rfl

これは内部的には `SPred` の略記であり、したがって `SPred` に関するすべての定理が適用されます。
-/
abbrev Assertion (ps : PostShape.{u}) : Type u :=
  SPred (PostShape.args ps)

/-
`H ⊢ₛ T` という形の検証条件（VC）が残る典型的なケースは、基底モナド `m` が多相（polymorphic）である場合です。
このとき、証明は `Assertion` 言語への翻訳を制御する `WP m ps` インスタンスに依存しますが、`σs : List (Type u)` との正確な対応関係はまだ未知です。

このような VC を解消するために、mvcgen には **Iris 並行分離論理（concurrent separation logic）** に着想を得た完全な証明モードが備わっています。
（実際、この証明モードはその Lean 版クローンである [**iris-lean**](https://github.com/leanprover-community/iris-lean) から多くの部分を取り入れています。）

Lean 4 のテストファイル [`tests/lean/run/spredProofMode.lean`](https://github.com/leanprover/lean4/blob/master/tests/lean/run/spredProofMode.lean) には、この証明モードの多くの例が含まれており、学習に役立ちます。
また、リファレンスマニュアルには、利用可能な証明モードタクティクの一覧が掲載されています。
-/

/-
## さらに調べたい人へ

* さらに多くの例が Lean のテストスイート内に見つかります。
  * [`tests/lean/run/doLogicTests.lean`](https://github.com/leanprover/lean4/blob/master/tests/lean/run/doLogicTests.lean) は、多数の例を詰め込んだ「なんでも入り（kitchen sink）」テストファイルです。
  * [`tests/lean/run/bhaviksSampler.lean`](https://github.com/leanprover/lean4/blob/master/tests/lean/run/bhaviksSampler.lean) は、Bhavik Mehta による大規模開発の一部を切り出したサンプルです。
  * Markus Himmel の [human-eval-lean](https://github.com/leanprover/human-eval-lean) プロジェクトには、命令的アルゴリズム実装に対する mvcgen ベースの証明がいくつか含まれています（コントリビューション歓迎とのことです！）。
  * また、Rish Vaishnav が進めている [qsort の形式化](https://github.com/rish987/qsort/) は、現在のところ mvcgen を用いた最大規模の例です。
* ぜひ次の項目のドキュメントコメントも読んでください：
  * `Std.Do.SPred`
  * `Std.Do.PostCond`
  * `Std.Do.PredTrans`
  * `Std.Do.Triple`
  * `mvcgen` タクティク
  * `mspec` タクティク
  * `mintro` タクティク
-/
