# Introduction

Computer algorithms are routinely deployed nowadays by all big stock
exchanges to match buy and sell requests. These algorithms are required
to comply with various regulatory guidelines. For example, it is
mandatory for a matching resulting from *call auctions*, a type of
double auction, to be *fair, uniform,* and *individual-rational*.

In this paper, we introduce a formal framework for analyzing trades
resulting from double auctions used in financial markets. To verify the
essential properties required by market regulators, we formally define
these notions in the functional setting of a theorem prover and then
develop important results about matching demand and supply. Finally, we
use this framework to verify properties of two important classes of
double auctions.

One of the resulting advantages of our work for an exchange or a
regulator is that they can automatically check the currently deployed
matching programs for any violations of required properties. All the
definitions and results presented in this paper are completely
formalized in the Coq Proof Assistant. The complete formalization in Coq
facilitates automatic program extraction in OCaml and Haskell, with the
guarantee that extracted programs satisfy the requirements specified by
the market regulator. Consequently, the extracted program could be
deployed directly at an exchange, in addition to being used for checking
violations in existing programs. We demonstrate the practical
applicability of our work by running the verified program on real market
data from an exchange to automatically check for violations in the
exchange algorithm.

To describe our contributions in detail, we first need to provide an
overview of double auctions.

## Overview of Double Auctions {#sec:overview}

Financial trades occur at various types of exchanges, such as those for
stocks, derivatives, commodities, and currencies. At any exchange,
multiple buyers and sellers participate in trading specific products.
Most exchanges use double auctions to match buyers and sellers.
Additionally, some exchanges use an online continuous algorithm to
execute trades during certain time intervals, particularly for highly
traded products.

To conduct trades of a certain product using a double auction, the
exchange collects buy and sell requests from traders over a fixed time
period. At the end of this period, the exchange matches some of these
requests and generates a *matching*, which is a set of *transactions*. A
buyer submits a buy request, also called a *bid*, specifying the maximum
quantity of units they wish to buy and a maximum price per unit that
they can pay. Similarly, a seller submits a sell request, known as an
*ask*, specifying a quantity and a minimum price per unit. Each
*transaction* consists of a bid, an ask, a transaction quantity, and a
transaction price. Naturally, the transaction quantity should be at most
the minimum of the bid and ask quantities, and the transaction price
should fall between the bid and ask prices, which is referred to as the
individual-rational property.

Apart from the individual-rational property, there are other desired
properties for the matching to possess. These properties are: *uniform*,
*fair*, *maximum*, and *optimal uniform*. We briefly describe these
matching properties:

-   **Uniform**: A matching is uniform if all its transaction prices are
    the same.

-   **Fair**: A bid $b_1$ is more competitive than a bid $b_2$ if $b_1$
    has a higher maximum price than $b_2$ or if their maximum prices are
    the same and $b_1$ arrives earlier than $b_2$. Similarly, we can
    define competitiveness between two asks. A matching is *unfair* if a
    less competitive bid gets matched but a more competitive bid is not
    fully matched. Similarly, it could be unfair if a more competitive
    ask is not fully matched. If a matching is not unfair, then it is
    fair.

-   **Maximum**: A matching is maximum if it has the largest volume (sum
    of the transaction quantities of all the transactions in the
    matching) among all possible matchings.

-   **Optimal-uniform**: A uniform matching is called optimal-uniform if
    it has the largest volume among all matchings that are uniform.

It is known that there are sets of bids and asks for which there is no
possible matching that possesses all the above properties simultaneously
(see, for example, [@WWW98; @mcafee1992]). This gives rise to two
classes of double auctions, each with a different objective:

1.  **Optimal-uniform matching**: In the context of financial markets,
    call auctions are commonly utilized where the matching needs to be
    fair and optimal-uniform, thus compromising on the maximum property.
    The common price in a matching produced by call auctions is often
    referred to as the equilibrium price, and the process is known as
    price discovery.

2.  **Maximum matching**: In other contexts where the matching being
    maximum is important, the matching needs to be fair and maximum,
    compromising on the uniformity property. Such double auctions are
    said to have dynamic-pricing.

In our work, we consider both these classes of double auctions.

## Our Contributions {#sec:contribution}

We now describe the results obtained in this work. For each result,
apart from describing the result informally, we also provide the formal
statement which involves terms that will be formally defined later.

-   **Combinatorial result.** We show that the modeling and the
    libraries we created to obtain our results are also useful in
    proving other important results on double auctions. For example, in
    Theorem [\[thm:boundM\]](#thm:boundM){reference-type="ref"
    reference="thm:boundM"}, we prove a well-known result (Lemma $4$ of
    [@NiuP13]): for any price $p$, no matching can achieve a volume
    higher than the sum of the total demand and the total supply in the
    market at price $p$. Here the total demand at a price $p$ is the sum
    of the quantities of the bids whose transaction price is at least
    $p$. Similarly, we can define total supply. Formally,

    ::: restatable
    theoremboundM[]{#thm:boundM label="thm:boundM"} If $M$ is a matching
    over an admissible order-domain $(B, A)$, then for all natural
    numbers $p$, we have
    $\mathsf{Vol}(M) \leq \mathsf{Vol}(B_{\geq p}) + \mathsf{Vol}(A_{\leq p})$.
    :::

    Here an admissible order-domain $(B, A)$ refers to a set of bids $B$
    and a set of asks $A$ with unique ids and unique timestamps. In our
    Coq formalization, this theorem appears as follows.

    ``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
    Theorem Bound p M B A: 
            admissible B A /\ Matching M B A -> 
            
            Vol(M) <= (Qty_orders (filter (fun x => p <= (oprice x)) B)) +
                      (Qty_orders (filter (fun x => p => (oprice x)) A)).
    (* Here Qty_orders(L) is the sum of the quantities of the orders in L. *)
    ```

-   **Fairness.** We show that any matching can be converted into a fair
    matching without compromising on the total volume. For this, we
    design an algorithm, the $\mathsf{Fair}$ procedure, which takes a
    matching $M$ as input, and outputs a matching $M'$. In Theorem
    [\[thm:Faircorrect\]](#thm:Faircorrect){reference-type="ref"
    reference="thm:Faircorrect"}, we show that the volume of $M$ and
    $M'$ are the same and $M'$ is a fair matching. Formally,

    ::: restatable
    theoremFaircorrect[]{#thm:Faircorrect label="thm:Faircorrect"} If
    $M$ is a matching over an admissible order-domain $(B, A)$, then the
    matching $M' = \mathsf{Fair}(M ,B ,A)$ over $(B,A)$ is a fair
    matching such that $\mathsf{Vol}(M) = \mathsf{Vol}(M')$.
    :::

    This theorem appears in our Coq formalization as follows.

    ``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
    (* Correctness of Fair proccedure *)
    Theorem Fair_main (M: list transaction) (B A: list order): 
            admissible B A /\ Matching M B A -> 
            
            (Matching (Fair M B A) B A) /\  
            (* (Fair M B A) is a matching over (B, A) *)
            (Vol(M)= Vol((Fair M B A))) /\  
            (* Trade volumes of M and (Fair M B A) are the same *)
            (Is_fair (Fair M B A) B A).     
            (* Process Fair produces a fair matching *)
    ```

-   **Uniform matching.** We design an algorithm, the $\mathsf{UM}$
    procedure, that takes as input a collection of bids and asks and
    outputs a fair and uniform matching. Furthermore, in Theorem
    [\[thm:UMcorrect\]](#thm:UMcorrect){reference-type="ref"
    reference="thm:UMcorrect"}, we show that the output matching has the
    largest total trade volume among all the matchings that are uniform
    and thus is optimal-uniform. This algorithm implements the call
    auction that is used at various exchanges. Formally,

    ::: restatable
    theoremUMcorrect[]{#thm:UMcorrect label="thm:UMcorrect"} Given an
    admissible order-domain $(B, A)$, $\mathsf{UM}(B ,A)$ outputs a fair
    and optimal-uniform matching over $(B,A)$.
    :::

    This theorem appears in our Coq formalization as follows.

    ``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
    (* The UM is fair and optimal uniform algorithm. *)
    Theorem UM_correct B A:
            admissible B A -> 
            Is_fair (UM B A) B A /\ Is_optimal_uniform (UM B A) B A.
    ```

-   **Maximum matching.** We design an algorithm, the $\mathsf{MM}$
    procedure, that takes as input a collection of bids and asks and
    outputs a fair and maximum matching. In Theorem
    [\[thm:MMcorrect\]](#thm:MMcorrect){reference-type="ref"
    reference="thm:MMcorrect"}, we show that the output matching has the
    largest volume among all the matchings. Formally,

    ::: restatable
    theoremMMcorrect[]{#thm:MMcorrect label="thm:MMcorrect"} Given an
    admissible order-domain $(B, A)$, $\mathsf{MM}(B,A)$ outputs a
    maximum volume matching over $(B, A)$ that is also fair.
    :::

    This theorem appears in our Coq formalization as follows.

    ``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
    (* The MM is fair and maximum volume matching algorithm. *)
    Theorem MM_correct B A:
            admissible B A -> 
            Is_maximum (MM B A) B A /\ Is_fair (MM B A) B A.
    ```

-   **Uniqueness theorems.** For any two fair and optimal-uniform
    matchings,
    Theorem [\[thm:uniquenessTheorem\]](#thm:uniquenessTheorem){reference-type="ref"
    reference="thm:uniquenessTheorem"} implies that for each order its
    total traded quantity in the two matchings is the same. Thus, if we
    compare the trade volumes between an exchange's matching output with
    our verified program's output and for some orders they do not match,
    then the exchange's matching is not fair and optimal-uniform.
    Conversely, if for each order, the trade volumes match, then
    Theorem [\[thm:ConverseUniquenessTheorem\]](#thm:ConverseUniquenessTheorem){reference-type="ref"
    reference="thm:ConverseUniquenessTheorem"} implies that the
    exchange's matching is also fair and optimal-uniform (given that it
    already a uniform matching, which can be easily verified by checking
    the transaction prices). Making use of these results,
    in [6.1](#sec:demonstration){reference-type="ref"
    reference="sec:demonstration"}, we check violations automatically in
    real data from an exchange.

    Formally,

    ::: restatable
    theoremuniquenessTheorem []{#thm:uniquenessTheorem
    label="thm:uniquenessTheorem"} Let $M_1$ and $M_2$ be two fair
    matchings over an admissible order domain $(B, A)$ such that
    $\mathsf{Vol}(M_1) = \mathsf{Vol}(M_2)$, then for each order
    $\omega$, the total traded quantity of $\omega$ in $M_1$ is equal to
    the total traded quantity of $\omega$ in $M_2$.
    :::

    ::: restatable
    theoremConverseUniquenessTheorem []{#thm:ConverseUniquenessTheorem
    label="thm:ConverseUniquenessTheorem"} Given a list of bids $B$ and
    a list of asks $A$, if $M_1$ is a fair matching and $M_2$ is an
    arbitrary matching such that for each order $\omega$, the total
    traded quantity of $\omega$ in $M_1$ is equal to the total traded
    quantity of $\omega$ in $M_2$, then $M_2$ is fair.
    :::

    These theorems appear in our Coq formalization as follows.

    ``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
    (* Uniqueness preperty (completeness) *)
    Theorem completeness M1 M2 B A:
            admissible B A /\ (Vol(M1) = Vol(M2)) /\
            (Matching M1 B A) /\ (Matching M2 B A) /\
            Is_fair M1 B A /\ Is_fair M2 B A ->

            (forall a, Qty_ask M1 (id a) = Qty_ask M2 (id a)) /\
            (forall b, Qty_bid M1 (id b) = Qty_bid M2 (id b)).

    (* Converse uniqueness preperty *)
    Theorem soundness M1 M2 B A:
            admissible B A /\ 
            (Matching M1 B A) /\ (Matching M2 B A) /\
            Is_fair M2 B A /\ (Vol(M1) = Vol(M2)) /\
            (forall a, Qty_ask M1 (id a) = Qty_ask M2 (id a)) /\
            (forall b, Qty_bid M1 (id b) = Qty_bid M2 (id b)) -> 

            Is_fair M1 B A.
    ```

    The above two theorems do not just help in building automated
    checkers for exchanges that output optimal-uniform matchings, but
    can similarly be utilized to build automated checkers for exchanges
    that output maximum matchings.

The Coq code together with the extracted OCaml and Haskell programs for
all the above results is available at [@git:call]. Our Coq formalization
consists of approximately 450 lemmas and theorems and 9000 lines of
code.

## Related Work {#sec:related}

In their influential work [@PI17], Passmore and Ignatovich emphasized
the importance of formal verification for financial algorithms and
identified several open problems in the field. In response, they
developed Imandra [@imandra], a specialized formal verification system
and programming language designed to reason about algorithmic properties
that can be proved, refuted, or described.

Wurman, Walsh, and Wellman discuss the theory and implementation of call
auctions in [@WWW98]. The fairness, uniform, maximum, and
optimal-uniform properties described above are discussed in the works of
Zhao, Zhang, Khan, and Perrussel [@zhao2010maximal] and Niu and
Parsons [@NiuP13]. The proofs and mechanisms discussed in these papers
are of single unit and not formalized. Besides this, many proofs
presented in [@NiuP13; @zhao2010maximal] are existential in nature.

In an earlier work [@SS20], Sarswat and Singh dealt primarily with
single unit trade requests and thus provided a proof of concept for
obtaining verified programs for financial markets. In this work, we
generalize their results to multiple units that results in verified
programs which can be directly used in real markets. Our proofs are
constructive and based on induction, which makes it easier to formalize.
Furthermore, the uniqueness theorems and the resulting automated
checkers that we present is a completely new contribution of this work.

As mentioned earlier, certain exchanges also use an online continuous
algorithm to match buy and sell requests. The theory, formalization, and
complexity of such auctions have been studied by Garg and Sarswat
in [@GS22; @kalpa]. Cervesato, Khan, Reis, and Žunić [@clf] use
concurrent linear logic (CLF) to outline two important properties of a
continuous trading system.

There are also some works formalizing various concepts from auction
theory [@KP18; @nash; @frank], particularly focusing on the Vickrey
auction mechanism.

In this work, we have significantly enhanced the formalization compared
to its preliminary version presented in [@RSS21]. The definitions and
algorithms have been streamlined, and the running time of our formalized
algorithms has improved from $O(n^2)$ to $O(n \log n)$ (where $n$
denotes the number of trade requests), which enhances the practical
applicability of our work.

## Organization of the Paper {#organization-of-the-paper .unnumbered}

The rest of this paper is organized as follows: In
[2](#sec:modeling){reference-type="ref" reference="sec:modeling"}, we
begin with the definitions of the various terms related to double
auctions. We then prove the demand-supply inequality
([\[thm:boundM\]](#thm:boundM){reference-type="ref"
reference="thm:boundM"}) in [3](#sec:demand-supply){reference-type="ref"
reference="sec:demand-supply"}. In [4](#sec:fair){reference-type="ref"
reference="sec:fair"}, we describe the $\mathsf{Fair}$ procedure and
establish its correctness
([\[thm:Faircorrect\]](#thm:Faircorrect){reference-type="ref"
reference="thm:Faircorrect"}). Next, in
[5](#sec:match){reference-type="ref" reference="sec:match"}, we describe
the $\mathsf{UM}$ and $\mathsf{MM}$ procedures and establish their
correctness
([\[thm:UMcorrect,thm:MMcorrect\]](#thm:UMcorrect,thm:MMcorrect){reference-type="ref"
reference="thm:UMcorrect,thm:MMcorrect"}). Finally, in
[6](#sec:uniqueness){reference-type="ref" reference="sec:uniqueness"},
we prove the uniqueness theorems
([\[thm:uniquenessTheorem,thm:ConverseUniquenessTheorem\]](#thm:uniquenessTheorem,thm:ConverseUniquenessTheorem){reference-type="ref"
reference="thm:uniquenessTheorem,thm:ConverseUniquenessTheorem"}) and
explain how they give rise to automated checkers for double auctions. A
practical demonstration of such a checker is also included in
[6.1](#sec:demonstration){reference-type="ref"
reference="sec:demonstration"}.

We have written our proofs and algorithms in a style that should be
accessible to a broader mathematical audience, including those
unfamiliar with concepts of formalization or functional programming. The
functional implementation of these algorithms is available in our
formalization [@git:call].

# Preliminaries {#sec:modeling}

In this section, we introduce the various definitions underlying our
formalization of double auctions. Many definitions in this work are
analogous to the definitions introduced for continuous double auctions
in [@GS22]. Our presentation leverages set notation for clarity, with
the understanding that all sets discussed are finite. It is worth noting
that our Coq formalization employs lists rather than sets. For brevity
and intuition, we apply set-theoretic notation (e.g., $\in$,
$\subseteq$, $\supseteq$, $\emptyset$) to lists, with their meanings
easily inferable from context. The decision to use lists in our
formalization serves two purposes: it aligns naturally with our auction
modeling, and crucially, it facilitates algorithm optimization, yielding
efficient implementations.

## Orders

Unlike a previous work [@RSS21], here we adopt a unified approach to
bids and asks by representing both as **orders**, eliminating redundant
proofs of shared properties. An order $\omega$ is defined as a 4-tuple
$(id, \ timestamp, \ quantity, \ price)$, where each component---denoted
as $\mathsf{id}(\omega)$, $\mathsf{timestamp}(\omega)$,
$\mathsf{qty}(\omega)$, and $\mathsf{price}(\omega)$ respectively---is a
natural number. Additionally, we stipulate that
$\mathsf{qty}(\omega) > 0$. It is important to note that prices are
expressed as natural numbers, corresponding to the smallest monetary
unit (e.g., cents in the United States).

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
(* Definition of Order in Coq. The term 'nat' stands for natural number*)
Record order := Make_order
            {id: nat; otime: nat; oquantity: nat; oprice: nat; 
            oquantity_cond: Nat.ltb oquantity 1 = false }.
(* The term (Nat.ltb x y) checks if x < y. *)
```

For a set of orders $\Omega$, we define $\mathsf{ids}(\Omega)$ as the
collection of all order ids that are in $\Omega$. For a set of orders
$\Omega$ with unique ids and an order $\omega \in \Omega$ where
$\mathsf{id}(\omega) = id$, we introduce the following syntactic sugar:
$\mathsf{timestamp}(\Omega,id)=\mathsf{timestamp}(\omega)$,
$\mathsf{qty}(\Omega,id)=\mathsf{qty}(\omega)$, and
$\mathsf{price}(\Omega, id)=\mathsf{price}(\omega)$. This shorthand is a
slight abuse of notation, but enhances readability in subsequent
discussions.

We now introduce the notion of an order-domain, the universe of bids and
asks in a given context, for example, the list of bids and asks that are
provided as input to a matching algorithm. We call $(B,A)$ to be an
order domain if $B$ and $A$ are sets of orders. Here, the first
component, $B$, represents the set of bids, while the second component,
$A$, represents the set of asks. We further define an **admissible**
order-domain as one where each order has a unique id and timestamp. In
the context of double auctions, any input to our algorithms consisting
of sets of bids and asks will invariably form an admissible
order-domain.

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
Definition admissible B A := 
            (NoDup (ids B))/\(NoDup (ids A))/\
            (NoDup (timesof B))/\(NoDup (timesof A)). 
(*Note: NoDup is predicate for duplicate-free and 
(timesof B) gives timestamp's of B*)
```

Let us now formalize the concepts of 'tradable' and 'matchable'.
Consider two orders: a bid $b$ and an ask $a$. We define these orders as
**tradable** if the bid price meets or exceeds the ask price, i.e.,
$\mathsf{price}(b) \geq \mathsf{price}(a)$. Extending this notion, we
characterize an order-domain as **matchable** if it contains a bid and
an ask that are tradable.

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
Definition tradable b a := (oprice b >= oprice a).

Definition matchable (B A : list order):= 
            exists b a, (In a A)/\(In b B)/\(tradable b a). 
            (* Term 'In' indicates membership *)
```

We now introduce the concept of competitiveness among orders. For bids,
we define a bid $b_1$ as more **competitive** than another bid $b_2$,
denoted as $b_1 \succ b_2$, under two conditions:

1.  The price of $b_1$ exceeds that of $b_2$
    ($\mathsf{price}(b_1) > \mathsf{price}(b_2)$), or

2.  The prices are equal, but $b_1$ has an earlier timestamp
    ($\mathsf{price}(b_1) = \mathsf{price}(b_2)$ and
    $\mathsf{timestamp}(b_1) < \mathsf{timestamp}(b_2)$).

Analogously for asks, we define an ask $a_1$ as more **competitive**
than $a_2$, denoted as $a_1 \succ a_2$, if:

1.  The price of $a_1$ is lower than that of $a_2$
    ($\mathsf{price}(a_1) < \mathsf{price}(a_2)$), or

2.  The prices are equal, but $a_1$ has an earlier timestamp
    ($\mathsf{price}(a_1) = \mathsf{price}(a_2)$ and
    $\mathsf{timestamp}(a_1) < \mathsf{timestamp}(a_2)$).

The notion of competitiveness will be useful while formalizing the
priority rule for double auctions.

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
Definition bcompetitive b b' := 
            ((oprice b') < (oprice b)) ||                                     
            (((oprice b') == (oprice b)) && ((otime b) <= (otime b'))).       
                                                                  
Definition acompetitive a a' := 
            ((oprice a) < (oprice a')) ||                                          
            (((oprice a) == (oprice a')) && ((otime a) <= (otime a'))).
```

## Transactions and Matchings

A transaction is a 4-tuple $(id_b, \ id_a, \ quantity, \ price)$, where
all components are natural numbers, $id_b$ and $id_a$ represents the ids
of the participating bid and ask, respectively, the $quantity$ specifies
the transaction quantity, and the $price$ denotes the transaction price.
We impose the constraint that $quantity > 0$ to ensure that the
transactions are meaningful. For a transaction $t$, we represent its
four components by $\mathsf{id_{bid}}(t)$, $\mathsf{id_{ask}}(t)$,
$\mathsf{qty}(t)$, and $\mathsf{tprice}(t)$, respectively.

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
Record transaction :=  Make_transaction 
        {idb: nat; ida: nat; tquantity: nat; tprice: nat; 
        tquantity_cond: Nat.ltb tquantity 1 = false }. 
```

::: remark*
**Remark 1**. *Both order and transaction are record types in our Coq
formalization. In our Coq definitions of these terms, oquantity_cond and
tquantity_cond ensure that no orders or transactions are allowed with a
quantity of zero. This restriction helps keeping the result statements
concise; for otherwise, we would have to add a condition stating these
quantities are positive in our results.*
:::

Let $T$ denote a set of transactions. We define $\mathsf{ids_{bid}}(T)$
and $\mathsf{ids_{ask}}(T)$ as the set of participating bid ids and ask
ids in $T$, respectively. Furthermore, we define three quantities.

1.  $\mathsf{Qty}_{\text{bid}}(T, id_b)$: The sum of the transaction
    quantities of transactions in $T$ where the participating bid has id
    $id_b$.

2.  $\mathsf{Qty}_{\text{ask}}(T, id_a)$: The sum of the transaction
    quantities of transactions in $T$ where the participating ask has id
    $id_a$.

3.  $\mathsf{Qty}_{\text{transaction}}(T, id_b \leftrightarrow id_a)$:
    The sum of the transaction quantities of transactions in $T$ where
    the participating bid and ask have ids $id_b$ and $id_a$,
    respectively.

For ease of readability, we simply use $\mathsf{Qty}$ to represent the
above quantities, where the exact meaning can be easily inferred from
context. We now define $\mathsf{Vol}(T)$ as the sum of the transaction
quantities of all transactions in $T$, and extend this notation to a set
or orders $\Omega$: $\mathsf{Vol}(\Omega)$ represents the sum of the
maximum quantities of the orders in $\Omega$.

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
(* Functional and propositional definitions of ids_bid *)
Definition fun_ids_bid T := uniq (map idb T).

(* Below, I represents ids of bids participating in T *)
Definition ids_bid I T := 
            (forall i, In i I ->(exists t, (In t T)/\(idb t = i))) /\
            (forall t, In t T ->(exists i, (In i I)/\(idb t = i))) /\
            (NoDup I).                                                  
            (* Similarly, we define ids_ask *)
```

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
(*Definition of Qty_bid and Qty_ask*)
Definition Qty_bid T i := 
           sum (map tquantity (filter (fun t => (idb t) == i) T)).
(* Sum of transaction quantities for all those transactions 
   whose bid id is equal to i. *)
(* Similarly, we define Qty_ask *)

Definition Qty_transaction T j i := 
           sum (map tquantity (filter (fun t => ((idb t) == j) &&
           (ida t) == i)) T)
```

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
(*Definition of Vol*)
Definition Vol T := sum (map tquantity T).
```

A transaction $t$ is said to be **over** an order-domain $(B,A)$ if its
participating bid and ask come from $(B,A)$, i.e.,
$\mathsf{id_{bid}}(t)$ $=$ $\mathsf{id}(b)$ for some bid $b\in B$ and
$\mathsf{id_{ask}}(t)=\mathsf{id}(a)$ for some ask $a\in A$.

A transaction $t$ is said to be **valid** with respect to an
order-domain $(B,A)$ if there exists bid $b\in B$ and ask $a\in A$
satisfying:

1.  $\mathsf{id_{bid}}(t) = \mathsf{id}(b)$ and
    $\mathsf{id_{ask}}(t) = \mathsf{id}(a)$

2.  $b$ and $a$ are tradable

3.  $\mathsf{qty}(t) \leq \min(\mathsf{qty}(b), \mathsf{qty}(a))$

4.  $\mathsf{price}(a) \leq \mathsf{tprice}(t) \leq \mathsf{price}(b)$

Note that condition 4 implies condition 2, but we keep both for clarity.
We say that a set of transactions $T$ is **valid** over $(B,A)$ if each
of its transactions is valid over $(B,A)$.

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
Definition Tvalid T B A := 
           forall t, (In t T) -> (exists b a, (In a A)/\(In b B)/\
           (idb t = id b)/\(ida t = id a)/\
           (tradable b a)/\
           (tquantity t <= oquantity b)/\(tquantity t <= oquantity a)/\
           (oprice b >= tprice t)/\(tprice t >= oprice a)).
```

We are now ready to define a matching, that represents a feasible set of
transactions that can arise from a given order-domain. We define a
**matching** $M$ over an admissible order-domain $(B,A)$ as a set of
valid transactions where for each order $\omega \in B \cup A$,
$\mathsf{Qty}(M, \mathsf{id}(\omega)) \leq \mathsf{qty}(\omega)$.

``` {.coq bgcolor="gray!07" fontsize="\\scriptsize"}
Definition Matching M B A := 
           (Tvalid M B A)/\
           (forall b, In b B -> (Qty_bid M (id b)) <= (oquantity b))/\
           (forall a, In a A -> (Qty_ask M (id a)) <= (oquantity a)).
```

## Classes of Matchings {#sec:TypesOfMatchings}

Now we defines specific matchings relevant to call auctions.

A matching $M$ over $(B, A)$ is called a **fair matching** if for each
order $\omega$ that gets traded in $M$, all orders that are more
competitive than $\omega$ are fully traded in $M$. Formally,
$$\begin{aligned}
    \text{a. } \ \forall &b,b'\in B, \ b \succ b' \text{ and } \mathsf{id}(b') \in \mathsf{ids_{bid}}(M) 
    \implies \mathsf{Qty}(M,id(b)) = \mathsf{qty}(b). \\
    \text{b. } \ \forall &a,a'\in A, \ a \succ a' \text{ and } \mathsf{id}(a') \in \mathsf{ids_{ask}}(M) 
    \implies \mathsf{Qty}(M,id(a)) = \mathsf{qty}(a) 
    
\end{aligned}$$ In the above definition, the first property is known as
fair on bids and the second property is known as fair on asks. A fair
matching is fair on the bids as well as fair on the asks.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
Definition Is_fair_bids M B :=
           forall b b', (In b B) /\ (In b' B) /\
           (bcompetitive b b' /\ ~eqcompetitive b b') /\   
           (* b is more competitive than b' *)
           (In (id b') (ids_bid_aux M)) ->                 
           (* b' participates in M *)
           (Qty_bid M (id b)) = (oquantity b).             
           (* b is fully traded in M *)

Definition Is_fair_asks M A :=
           forall a a', (In a A) /\ (In a' A) /\ 
           (acompetitive a a' /\ ~eqcompetitive a a') /\
           (In (id a') (ids_ask_aux M)) ->
           (Qty_ask M (id a)) = (oquantity a).

Definition Is_fair M B A := 
           Is_fair_bids M B /\ Is_fair_asks M A.  
           (* M is fair over (B, A). *)
```

Note that, as we will see later in [4](#sec:fair){reference-type="ref"
reference="sec:fair"}, for a given matching $M$ over $(B, A)$ there
always exists a matching $M'$ over $(B, A)$ such that $M'$ is fair and
$\mathsf{Vol}(M)=\mathsf{Vol}(M')$.

A matching $M$ over $(B, A)$ is called a **maximum matching** if it has
the highest volume among all matchings over $(B,A)$, i.e., for all
matchings $M'$ over $(B,A)$, $\mathsf{Vol}(M) \ge \mathsf{Vol}(M')$.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
Definition Is_max M B A := Matching M B A ->
           forall M', Matching M' B A /\ Vol(M) >= Vol(M').
```

Note that there can be multiple maximum matchings over an order-domain.
In Section [5.2](#sec:maximum){reference-type="ref"
reference="sec:maximum"} we will see an algorithm that takes an
order-domain as input and outputs a maximum matching over it, which is
also fair.

Assigning different transaction prices for the same product at the same
point in time might make some traders unhappy. Consequently, it is
desirable that all the transactions have the same transaction price. A
matching where each transaction price is the same is called a **uniform
matching**.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
Definition Is_uniform M B A := (Uniform M /\ Matching M B A). 
(* Here Uniform is an inductive predicate that checks 
if the trade prices of M are all equal. *)
```

<figure id="fig:mmum">
<div class="center">
<p><span>!</span></p>
</div>
<figcaption>Sometimes to maximize the total trade volume, we have to
accept different trade prices to the matched bid-ask pairs. In this
example the only matching of size two is not uniform. Here the bids (B)
and the asks (A) all have quantity one each, and their limit prices are
displayed.</figcaption>
</figure>

A matching $M$ over $(B, A)$ is called an **optimal uniform** matching
if $M$ is uniform and has the maximum volume among all the uniform
matchings over $(B, A)$.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}

Definition Is_optimal_uniform M B A := Is_uniform M B A -> 
           forall M', Is_uniform M' B A /\ Vol(M) >= Vol(M').
```

Note that the volume of an optimal uniform matching can be strictly less
than the volume of a maximum matching (see
[1](#fig:mmum){reference-type="ref" reference="fig:mmum"}). Also,
similar to the case of maximum matchings, there can be more than one
optimal uniform matchings over a given order-domain. In
Section [5.1](#sec:uniform){reference-type="ref"
reference="sec:uniform"}, we exhibit an algorithm that takes as input an
order-domain and outputs an optimal uniform matching, which is also
fair.

# Demand-Supply Inequality {#sec:demand-supply}

Now we are ready to present the proof of the demand-supply inequality,
which provides an upper bound on the volume of an arbitrary matching in
terms of the *demand* and *supply*. This is a basic inequality that is
of independent interest and serves as a good warm-up before we delve
into double auctions.

Given a list of bids $B$ and a list of asks $A$, where the ids are all
distinct, i.e., $(B,A)$ forms an admissible domain, we first define what
we mean by the total demand/supply at price $p$. To this end, let
$B_{\geq p}$ represent the list of bids in $B$ whose limit prices are at
least $p$ and $A_{\leq p}$ represents the list of asks in $A$ whose
limit prices are at most $p$. The total demand at price $p$ is defined
to be the sum of the quantities of orders in $B_{\geq p}$, i.e.,
$\mathsf{Vol}(B_{\geq p})$. Similarly, the total supply at price $p$ is
defined to be the sum of the quantities of the orders in $A_{\leq p}$,
i.e., $\mathsf{Vol}(A_{\leq p})$. We can now state the theorem as
follows.

This appears in the Coq formalization as

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
Theorem Bound p M B A: 
        admissible B A /\ Matching M B A -> 
        
        Vol(M) <= (Qty_orders (filter (fun x => p <= (oprice x)) B)) +
                  (Qty_orders (filter (fun x => p => (oprice x)) A)).
(* Here Qty_orders(L) is the sum of the quantities of the orders in L. *)
```

::: proof
*Proof of [\[thm:boundM\]](#thm:boundM){reference-type="ref"
reference="thm:boundM"}.* First observe that the volume of any matching
is upper bounded by the volume of all bids as well as the volume of all
asks, i.e., if $M$ is a matching over $(B,A)$, then

$$\begin{aligned}
\mathsf{Vol}(M) 
\le \mathsf{Vol}(B)\quad\text{ and } \quad\mathsf{Vol}(M) \le \mathsf{Vol}(A).
\end{aligned}$$

To prove the Theorem [\[thm:boundM\]](#thm:boundM){reference-type="ref"
reference="thm:boundM"}, we partition the matching $M$ into two sets:
$M_1=\{(b,a,q,p') \in M \mid  \mathsf{price}(b) \geq p\}$ and
$M_2=\{(b,a,q,p') \in M \mid  \mathsf{price}(b) < p\}$. Thus,
$\mathsf{Vol}(M) = \mathsf{Vol}(M_1) + \mathsf{Vol}(M_2)$.

It is easy to see that $M_1$ is a matching over sets of bids
$B_{\geq p}$ and asks $A$, and hence from the above observation,

$$\begin{aligned}
\mathsf{Vol}(M_1) \leq \mathsf{Vol}(B_{\geq p}).
\end{aligned}$$

Next, we prove that $M_2$ is a matching over sets of bids $B$ and asks
$A_{< p}$. Consider a transaction $m=(b,a,q,p')$ from $M_2$. Since
$m \in M$, $\mathsf{price}(b) \ge \mathsf{price}(a)$, and from the
definition of $M_2$, we have $\mathsf{price}(b) < p$. This implies
$\mathsf{price}(a) < p$, i.e., asks of $M_2$ come from $A_{< p}$. Hence,
$M_2$ is a matching over $(B,A_{< p})$, and applying the above
observation again, we have

$$\begin{aligned}
\mathsf{Vol}(M_2) \le \mathsf{Vol}(A_{< p}).
\end{aligned}$$

Combining, we have

$$\begin{aligned}
\begin{aligned}
\mathsf{Vol}(M) &=  \mathsf{Vol}(M_1) + \mathsf{Vol}(M_2) \\ 
        &\leq \mathsf{Vol}(B_{\ge p}) + \mathsf{Vol}(A_{< p}) \quad\quad\quad\text{ using (2) and (3)} \\ 
        &\leq \mathsf{Vol}(B_{\ge p}) + \mathsf{Vol}(A_{\leq p}),
\end{aligned}
\end{aligned}$$

which completes the proof of
[\[thm:boundM\]](#thm:boundM){reference-type="ref"
reference="thm:boundM"}. ◻
:::

Formalization notes: The above proof is formalized in the file
'Demand_supply_Inequality.v'.

# The $\mathsf{Fair}$ Algorithm {#sec:fair}

In this section, we show that there exists an algorithm, which we refer
to as the $\mathsf{Fair}$ procedure, that takes an admissible
order-domain $(B, A)$ and a matching $M$ over $(B,A)$ and outputs a fair
matching $M' = \mathsf{Fair}(M, B, A)$ over $(B,A)$ with the same volume
as that of $M$, i.e., $\mathsf{Vol}(M) = \mathsf{Vol}(M')$.

The $\mathsf{Fair}$ procedure, given an input consisting of an
admissible order-domain $(B,A)$ and a matching $M$ over $(B,A)$ works in
two steps: In the first step, a procedure called $\mathsf{FOB}$ is
applied that takes $M$ and $B$ as input and outputs a matching $M'$ over
$(B,A)$ which is fair on the bids and has the same volume as that of
$M$. In the second step, a procedure called $\mathsf{FOA}$ is applied
that takes the resulting matching $M'$ and $A$ as input and outputs a
matching $M''$ over $(B,A)$ which is fair on the asks and has the same
volume as that of $M'$. The $\mathsf{Fair}$ procedure, which is the
composition of the procedures $\mathsf{FOA}$ and $\mathsf{FOB}$, returns
$M''$ as its output which has the same volume as $M$ and is fair (on
both the bids and the asks).

The procedures $\mathsf{FOB}$ and $\mathsf{FOA}$, along with their
correctness proofs, mirror each other and we just describe
$\mathsf{FOA}$ below. We show that the $\mathsf{FOA}$ procedure outputs
a fair on asks matching with the same volume as that of the input
matching. Furthermore, if the input matching is fair on the bids, then
the output matching of the $\mathsf{FOA}$ procedure continues to be fair
on the bids. This will immediately imply that the procedure
$\mathsf{Fair}(M,B,A)$ outputs a fair matching over $(B,A)$ with the
same volume as that of $M$.

## Fair on Asks

The $\mathsf{FOA}$ procedure given a matching $M$ over $(B,A)$ and the
list of asks $A$, sorts the asks in $A$ in decreasing order of
competitiveness (in particular, the most competitive ask is brought to
the top) and sorts the transactions in the matching $M$ in increasing
order of transaction prices. Then, its calls an auxiliary procedure
$\mathsf{FOA_{aux}}$ that produces a fair on ask matching.

::: algorithm
::: algorithmic
Sort the transactions in $M$ in increasing order of its transaction
prices Sort the asks in $A$ in decreasing order of competitiveness.
:::
:::

Intuitively, when all the asks are of unit quantity, we want to scan the
sorted list of the transactions $M$ from top to bottom replacing the ask
ids therein with the ask ids of $A$ from top to bottom. Note that the
transaction prices in $M$ will remain unchanged. This will produce a
fair on asks matching. In the $\mathsf{FOA}$ procedure, we will
implement this intuition. We just need to take care of multiple quantity
asks and transactions. Furthermore, we want to make the procedure
recursive so that we can provide a formalization friendly inductive
proof of correctness.

::: algorithm
::: algorithmic
$m \leftarrow \mathsf{pop}(M)$ $a \leftarrow \mathsf{pop}(A)$
$m' \leftarrow (\mathsf{id_{bid}}(m),\mathsf{id}(a), \min\{\mathsf{qty}(m),\mathsf{qty}(a)\}, \mathsf{price}(m))$
$\mathsf{push}(M_\alpha, m')$
$a \leftarrow (\mathsf{id}(a),\mathsf{timestamp}(a),\mathsf{qty}(a) - \mathsf{qty}(m),\mathsf{price}(a))$
$\mathsf{push}(A, a)$
$m \leftarrow (\mathsf{id_{bid}}(m),\mathsf{id_{ask}}(m), \mathsf{qty}(m) - \mathsf{qty}(a), \mathsf{price}(m))$
$\mathsf{push}(M, m)$ $\mathsf{FOA_{aux}}(M, A, M_\alpha)$
:::
:::

We initialize $M_\alpha$ to be an empty list, which at the end of the
procedure will form the output. After the sorting steps, we first remove
the top ask $a$ of $A$ and the top transaction $m$ of $M$. We then
produce the transaction $m'$ of quantity
$\min\{\mathsf{qty}(m),\mathsf{qty}(a)\}$ between the bid of $m$ and the
ask $a$. We add $m'$ to the list $M_\alpha$. We then compare the
quantities $\mathsf{qty}(m)$ and $\mathsf{qty}(a)$ to update the lists
$M$ and $A$ appropriately and then recursively solve the problem on the
updated lists $M$ and $A$. In the case
$\mathsf{qty}(m)=\mathsf{qty}(a)$, we neither update $A$ nor $M$. In the
case $\mathsf{qty}(m) < \mathsf{qty}(a)$, we reduce the quantity of ask
$a$ by $\mathsf{qty}(m)$ and insert this updated $a$ into the list $A$.
Finally, in the case $\mathsf{qty}(m)>\mathsf{qty}(a)$, we reduce the
transaction quantity of $m$ by $\mathsf{qty}(a)$ and insert this updated
$m$ into the list $M$. The procedure terminates when either $A$ or $M$
becomes empty. Note that since the
$\mathsf{Vol}(M) \leq \mathsf{Vol}(A)$, $A$ cannot become empty before
$M$ becomes empty.

Having defined the $\mathsf{FOA}$ procedure, now we state the
correctness theorem for $\mathsf{FOA}$. We need to show that the
matching $M_\alpha$ produced by $\mathsf{FOA}$ is fair on the asks and
the total volume of the input matching $M$ is the same as that of the
output matching $M_\alpha$. We also need to show that the $\mathsf{FOA}$
procedure does not alter the fairness on the bids, i.e., if the input
matching $M$ is fair on the bids, then the output matching $M_\alpha$
remains fair on the bids.

::: {#thm:FOA .theorem}
**Theorem 1**. *Let $M$ be a matching over an admissible order-domain
$(B, A)$. If $M_\alpha = \mathsf{FOA}(M, A)$, then the following hold.*

1.  *$M_\alpha$ is a matching over $(B, A)$.*

2.  *$\mathsf{Vol}(M) = \mathsf{Vol}(M_\alpha)$.*

3.  *$M_\alpha$ is fair on the asks.*

4.  *For each bid $b \in B$,
    $\mathsf{Qty}(M,id(b)) = \mathsf{Qty}(M_\alpha, id(b))$.*
:::

As a corollary of the last part above, we get that if $M$ is fair on the
bids, then $M_\alpha$ is also fair on the bids.

The theorem statement appears in our Coq formalization as follows.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* The fair on ask correctness lemma. *)
Lemma FOA_correct B A:
      admissible B A /\ Matching M B A ->
      Matching (FOA M A) B A /\
      (* (a) *)
      Vol(M) = Vol(FOA M A) /\
      (* (b) *)
      Is_fair_asks (FOA M A) A /\
      (* (c) *)
      (forall b, In b B -> Qty_bid M id(b) = Qty_bid (FOA M A) id(b)).
      (* (d) *)
```

::: proof
*Proof of [1](#thm:FOA){reference-type="ref" reference="thm:FOA"}.* We
give an outline of the proof, which has several obvious parts, focusing
only on the most intricate aspect.

**Proof of (a):** To prove that $M_\alpha$ is a matching, we need to
show the following.

-   The ids of the bids and asks that participate in $M_\alpha$ come
    from $B$ and $A$, respectively.

-   For each transaction $m$ in $M_\alpha$ between the bid $b$ and ask
    $a$, the transaction quantity of $m$ is at most $\mathsf{qty}(b)$
    and at most $\mathsf{qty}(a)$.

-   For each order $\omega$ in $B\cup A$, its total traded quantity in
    $M_\alpha$ is at most its total quantity $\mathsf{qty}(\omega)$.

-   For each transaction $m$ in $M_\alpha$ which is between a bid $b$
    and an ask $a$, the transaction price of $m$ is between the limit
    prices of $b$ and $a$, i.e.,
    $\mathsf{price}(a) \leq \mathsf{tprice}(m) \leq \mathsf{price}(b)$.

It is easy to verify that (i), (ii), (iii), and
$\mathsf{tprice}(m) \leq \mathsf{price}(b)$ of (iv) hold, as
$\mathsf{FOA}$ always respects these constraints. The difficult part is
showing $\mathsf{price}(a) \leq \mathsf{tprice}(m)$ of (iv), where we
have to prove that when an ask id is replaced from a transaction $m$ by
an ask id of an ask $a$ in $A$, the transaction price
$\mathsf{tprice}(m)$ is at least $\mathsf{price}(a)$. In other words, we
need to show why the transaction prices of $M$ are respected by the
replaced asks.

For ease of readability, we will not keep the list of output
transactions in the argument of $\mathsf{FOA_{aux}}$, i.e., we will
write $\mathsf{FOA_{aux}}(M,A)$ instead of
$\mathsf{FOA_{aux}}(M,A,M_\alpha)$. Let $M$ be a matching over $(B,A)$
which is sorted by increasing transaction prices and $A$ is sorted by
decreasing competitiveness, i.e., the ask with the smallest price is on
top of $A$. We need to show that for each transaction $m$ in
$M_\alpha=\mathsf{FOA_{aux}}(M,A)$ if the ask participating in $m$ is
$a$ then $\mathsf{price}(a)\leq \mathsf{tprice}(m)$. We will show this
by induction on $|M|+|A|$ (note that in each recursive call of
$\mathsf{FOA_{aux}}$ either the size of the first argument $|M|$
decreases or the size of the second argument $|A|$ decreases). In fact,
we will show a slightly general statement:

::: claim*
**Claim 1**. *If $M$ is a matching over some admissible order-domain
$(\hat B,\hat A)$ and $M$ and $A$ have the *supply property* (defined
below), then for each transaction in $M_\alpha=\mathsf{FOA_{aux}}(M,A)$
whose participating ask is $a\in A$,
$\mathsf{price}(a)\leq \mathsf{tprice}(m)$.*
:::

Note that $A$ need not be the same as $\hat A$ in the above statement.
This strengthening is crucial for our proof to work, as when
$\mathsf{FOA_{aux}}(M,A)$ makes a recursive call to
$\mathsf{FOA_{aux}}(M',A')$, then $M'$ might have participating asks
that are not present in $A'$.

**Supply property:** Let us now define the supply property. We say a
matching $M$ (over an arbitrary admissible order-domain) and asks $A$
have the supply property if
$$\mathsf{Vol}(A_{\le p}) \geq \mathsf{Vol}(M_{\leq p}),$$ for all
transaction prices $p$ in $M$, where
$A_{\leq p} = \{a\in A \mid \mathsf{price}(a)\leq p\}$ and
$M_{\leq p}=\{m \in M \mid \mathsf{tprice}(m) \leq p\}$.

Observe that if $M$ is over $(B,A)$, then $M$ and $A$ trivially satisfy
the supply property since all transactions in $M$ with transaction
prices at most $p$ have participating asks from $A$ whose prices are at
most $p$. Thus, showing the claim is enough to complete this part of the
proof.

Let $m$ be the top transaction in $M$, i.e., with the smallest
transaction price, and $a$ be the most competitive ask in $A$, i.e., the
one with the smallest limit price. Notice that when
$\mathsf{FOA_{aux}}(M,A)$ is called it first outputs a transaction $m'$
of quantity $q=\min\{\mathsf{qty}(m),\mathsf{qty}(a)\}$, transaction
price $p=\mathsf{tprice}(m)$, where the participating bid is the bid of
$m$ and the participating ask is $a$. Here clearly,
$\mathsf{price}(a) \leq p=\mathsf{tprice}(m)$, as $a$ is the most
competitive ask and there exists an ask in $A$ with price at most $p$ as
from the supply property
$\mathsf{Vol}(A_{\leq p}) \geq \mathsf{Vol}(M_{\leq p})\geq \mathsf{qty}(m)> 0$.

Now the remaining transactions output by $\mathsf{FOA_{aux}}$ are
obtained from the recursive call made on $\mathsf{FOA_{aux}}(M',A')$,
where $M'$ is obtained from $M$ by the reducing quantity $q$ from $m$
(if $q=\mathsf{qty}(m)$, $m$ is deleted from $M$), and $A'$ is obtained
from $A$ by reducing the quantity of $a$ by $q$ (if $q=\mathsf{qty}(a)$,
$A$ is deleted from $A$). As noted earlier, $|M'|+|A'|\leq |M|+|A|$. We
will now be immediately done with induction. To apply the induction,
however, we need to show that $M'$ and $A'$ satisfy the supply property.
This is easy to deduce as initially $M$ and $A$ satisfied the supply
property, and $q$ quantity was reduced from both $M$ and $A$ which had
the lowest prices, at most the smallest transaction price
$\mathsf{price}(m)$, to obtain $M'$ and $A'$; this will imply that $M'$
and $A'$ continue to have the supply property: for each transaction
price $p$ of $M'$, we have

$$\mathsf{Vol}(A_{\le p}) \geq \mathsf{Vol}(M_{\leq p}) 
\implies  \mathsf{Vol}(A_{\le p}) -q \geq \mathsf{Vol}(M_{\leq p}) -q \implies  \mathsf{Vol}(A'_{\le p})\geq \mathsf{Vol}(M'_{\leq p}).$$

This completes the proof of (a). Proofs of (b), (c), and (d) follow
straightforwardly. To see part (b), notice that
$\mathsf{Vol}(A)\geq \mathsf{Vol}(M)$, and the algorithm will be able to
replace every transaction in $M$ with asks in $A$. Part (c) also follows
immediately, since the most competitive asks are given priority by the
algorithm. Part (d) follows from observing that the bids and their
quantities that participate in $M$ remain completely unaltered by
$\mathsf{FOA}$. ◻
:::

As explained earlier, similar to the $\mathsf{FOA}$ procedure, we have
the $\mathsf{FOB}$ procedure, that produces a matching that is fair on
the bids. Combining the $\mathsf{FOB}$ and $\mathsf{FOA}$ procedures, we
have the following definition of the $\mathsf{Fair}$ procedure.
$$\mathsf{Fair}(M ,B ,A) =  \mathsf{FOA}(\mathsf{FOB}(M, B), A)$$.

::: remark*
**Remark 2**. *Note that we could have also chosen a different
definition for $\mathsf{Fair}$. Namely,
$$\mathsf{Fair}(M, B, A) = \mathsf{FOB}(\mathsf{FOA}(M, A),B).$$ Let
$M_1 = \mathsf{FOA}(\mathsf{FOB}(M, B), A)$ and
$M_2 = \mathsf{FOB}(\mathsf{FOA}(M, A), B)$. Both $M_1$ and $M_2$ can be
proven to be fair matchings with the same total volume. Furthermore,
later in [6](#sec:uniqueness){reference-type="ref"
reference="sec:uniqueness"} we will prove
[\[thm:uniquenessTheorem\]](#thm:uniquenessTheorem){reference-type="ref"
reference="thm:uniquenessTheorem"}, which, in particular, implies that
for each order $\omega$, the total traded quantity of $\omega$ in $M_1$
is equal to the total traded quantity of $\omega$ in $M_2$.*

*Notice that in producing both $M_1$ and $M_2$, the initial matching and
the intermediate matching are sorted based on transaction prices: once
while applying $\mathsf{FOA}$ and once when applying $\mathsf{FOB}$. It
is easy to see that if the sorting done during $\mathsf{FOA}$ and
$\mathsf{FOB}$ are *consistent*, that is, if the second sort on the
intermediate matching results in the list of transactions being
reversed, then $M_1 = M_2$. In particular, if the transaction prices in
the initial matching $M$ are all distinct, then the two sorts will
always be consistent, and hence $M_1=M_2$.*

*However, the matchings $M_1$ and $M_2$ may not be the same if the two
sorting steps are not consistent. An easy way to see an example of this
is to imagine a matching $M$ where all transaction prices are the same,
and all the bids in $B$ and asks in $A$ are of unit quantity and get
completely traded in $M$; in particular, $|M|=|A|=|B|$. Since all
transaction prices are identical, permuting $M$ in any order is a valid
sorting. Let us assume that the sorting outputs a uniformly random
permutation of the input list. In that case each of $M_1$ and $M_2$ will
be a uniformly random pairing of the bids $B$ and the asks $A$, and
$M_1=M_2$ will occur with a probability of only $\frac{1}{|B|!}$. *
:::

We conclude this section by formally summarizing our main result on the
$\mathsf{Fair}$ procedure.

This theorem statement appears in our Coq formalization as follows.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* Correctness of Fair procedure. *)
Theorem Fair_main (M: list transaction) (B A: list order): 
        admissible B A /\ Matching M B A -> 
        
        (Matching (Fair M B A) B A) /\  
        (* (Fair M B A) is a matching over (B, A) *)
        (Vol(M)= Vol((Fair M B A))) /\  
        (* Trade volumes of M and (Fair M B A) are the same *)
        (Is_fair (Fair M B A) B A).     
        (* Process Fair produces a fair matching *)
```

Formalization notes: The procedure $\mathsf{FOB}$ and $\mathsf{FOA}$ are
implemented in Coq using the Equations plugin which is helpful to write
functions involving well-founded recursion [@equation]. The proof of
Theorem [\[thm:Faircorrect\]](#thm:Faircorrect){reference-type="ref"
reference="thm:Faircorrect"} is done in several parts. First, we prove
all the parts of [1](#thm:FOA){reference-type="ref" reference="thm:FOA"}
in the file 'Fair_Ask.v'. We prove similar theorems for the procedure
$\mathsf{FOB}$ in 'Fair_Bid.v' file. Later all the results are combined
in the file 'Fair.v' and the above theorem is proved as *Fair_exists*.

# Matching Algorithms {#sec:match}

In this section, we formalize two almost identical $O(n \log n)$ time
algorithms for the maximum matching and the optimal uniform matching
problems. These algorithms start with sorting the list of bids in
decreasing order of competitiveness. Next, the list of asks is sorted
based on competitiveness: for maximum matching in increasing order,
whereas, for optimal uniform matching, in decreasing order. After the
sorting step, both algorithms work in linear time using the
$\mathsf{Match}$ subroutine as follows (See
Algorithm [\[algo:match\]](#algo:match){reference-type="ref"
reference="algo:match"}). The bid $b$ on top of its sorted list is
matched with the ask $a$ on top of its sorted list if they are tradable,
i.e., $\mathsf{price}(b) \ge \mathsf{price}(a)$. In this case, a
transaction between them is established with transaction quantity
$q= \min(\mathsf{qty}(b),q(a))$ and transaction price
$\mathsf{price}(a)$;[^2] a quantity of $q$ is reduced from their
existing quantities; finally, the $0$ quantity orders are deleted from
the lists. If the orders $b$ and $a$ are not matchable, ask $a$ is
deleted. The above steps are then repeatedly applied until one of the
lists becomes empty.[^3] Finally, for uniform price matching, all
transaction prices are replaced by the transaction price of the last
transaction, which can be achieved in linear time (this step is not done
by $\mathsf{Match}$).

::: algorithm
[]{#algo:match label="algo:match"}

::: algorithmic
$b\leftarrow \mathsf{pop}(B)$ $a\leftarrow \mathsf{pop}(A)$

$\mathsf{push}(B, b)$ $\mathsf{Match}(B, A, M)$

$q\leftarrow \min\{\mathsf{qty}(a),\mathsf{qty}(b)\}$
$\mathsf{push}(M, \{(\mathsf{id}(b),\mathsf{id}(a), q, \mathsf{price}(a))\})$
$\mathsf{push}(B,(\mathsf{id}(b),\mathsf{timestamp}(b),\mathsf{qty}(b)-q,\mathsf{price}(b)))$

$\mathsf{push}(A,(\mathsf{id}(a),\mathsf{timestamp}(a),\mathsf{qty}(a)-q,\mathsf{price}(a)))$

$\mathsf{Match}(B,A,M)$
:::
:::

We are going to prove the correctness of optimal uniform and maximum
matching algorithms separately in the next two subsections. Since both
these algorithms use the $\mathsf{Match}$ subroutine, we first describe
some important properties about $\mathsf{Match}$ that will be used
later.

We begin with observing three properties of the $\mathsf{Match}$
subroutine.

::: {#lem:match_matching .proposition}
**Proposition 2**. *If $(B, A)$ is an admissible order domain, then
$\mathsf{Match}(B,A,\emptyset)$ outputs a matching over $(B,A)$.*
:::

::: {#lem:match_fob .proposition}
**Proposition 3**. *If $(B, A)$ is an admissible order-domain and $B$ is
sorted in decreasing competitiveness of the bids, then
$\mathsf{Match}(B,A,\emptyset)$ outputs a matching that is fair on the
bids.*
:::

::: {#lem:match_foa .proposition}
**Proposition 4**. *If $(B, A)$ is an admissible order-domain and $A$ is
sorted in decreasing competitiveness of the asks, then
$\mathsf{Match}(B,A,\emptyset)$ outputs a matching that is fair on the
asks.*
:::

In our Coq formalization, these propositions appear as follows.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* The Match subroutine outputs a matching over (B, A). *)
Lemma Match_Matching B A:
      admissible B A -> Matching (Match B A) B A.
```

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* The Match subroutine outputs a fair on bids matching. *)
Lemma Match_Fair_on_Bids B A:
      admissible B A /\ Sorted bcompetitive B -> Is_fair_bids (Match B A) B.
```

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* The Match subroutine outputs a fair on asks matching. *)
Lemma Match_Fair_on_Asks B A:
      admissible B A /\ Sorted acompetitive A -> Is_fair_asks (Match B A) A.
```

The proofs of these propositions are quite straightforward and we omit
the tedious details here.

Next, we prove one of the main lemmas for the $\mathsf{Match}$
subroutine that will be crucially used in establishing the optimality of
our uniform matching algorithm in the next subsection.

::: {#lem:match_optimal_um .lemma}
**Lemma 1**. *If $(B, A)$ is an admissible order-domain and bids of $B$
and asks of $A$ are sorted by decreasing competitiveness, then
$M = \mathsf{Match}(B, A,\emptyset)$ outputs a matching whose volume is
at least the volume of an optimum uniform matching over $(B,A)$, i.e.,
for all uniform matching $M'$ over $(B, A)$,
$\mathsf{Vol}(M) \ge \mathsf{Vol}(M')$.*
:::

In our Coq formalization, this lemma appears as follows.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* The Match is optimal uniform when B and A are sorted by competitiveness. *)
Theorem Match_optimal_um B A:
        admissible B A /\ 
        Sorted bcompetitive B /\ Sorted acompetitive A /\ 
        Is_uniform M B A -> 
        Vol(Match B A) >= Vol(M).
```

To prove the above lemma, we will use the following lemma which states
that if $M$ is a uniform matching over $(B, A)$ with total volume at
least the minimum of quantities of the most competitive bid $b\in B$ and
the most competitive ask $a\in A$, then there exists a uniform matching
$M_{ab}$ of the same volume containing a transaction between $b$ and $a$
with transaction quantity precisely
$\min\{\mathsf{qty}(a),\mathsf{qty}(b)\}$ (the maximum possible trade
between $b$ and $a$).

::: {#lem:surgery1 .lemma}
**Lemma 2**. *Let $b$ and $a$ be the most competitive bid and ask in $B$
and $A$, respectively. If $M$ is a uniform matching over $(B, A)$ such
that $\mathsf{Vol}(M) \ge \min(\mathsf{qty}(b),\mathsf{qty}(a))$, then
there exists a uniform matching $M_{ab}$ over $(B, A)$ such that
$\mathsf{Vol}(M) = \mathsf{Vol}(M_{ab})$ and $M_{ab}$ contains a
transaction between $b$ and $a$ with quantity
$\min\{\mathsf{qty}(b),\mathsf{qty}(a)\}$.*
:::

We first prove [1](#lem:match_optimal_um){reference-type="ref"
reference="lem:match_optimal_um"} assuming
[2](#lem:surgery1){reference-type="ref" reference="lem:surgery1"}, which
will be proved subsequently.

::: proof
*Proof of [1](#lem:match_optimal_um){reference-type="ref"
reference="lem:match_optimal_um"}.* Let $(B,A)$ be an admissible
order-domain, where $B$ and $A$ are sorted by decreasing
competitiveness. Let $M=\mathsf{Match}(B,A,\emptyset)$, and let $M'$ be
an arbitrary uniform matching over $(B,A)$. We need to show that
$\mathsf{Vol}(M)\geq\mathsf{Vol}(M')$. We prove this by induction on
$(|B| + |A|)$. In the base case, $B = \emptyset$ or $A = \emptyset$,
which implies $\mathsf{Vol}(M')=0$, and we are trivially done.

Induction step: $|B|\geq 1$ and $|A|\geq 1$. $\mathsf{Match}$ first
removes the top orders $b$ and $a$ from $B$ and $A$, respectively, and
compares their prices. Since both $B$ and $A$ are sorted, $b$ is the
most competitive bid of $B$ and $a$ is the most competitive ask of $A$.
We have two cases: $\mathsf{price}(b) < \mathsf{price}(a)$ and
$\mathsf{price}(b) \ge \mathsf{price}(a)$. In the first case, when
$\mathsf{price}(b) < \mathsf{price}(a)$, since the most competitive bid
$b$ of $B$ is not tradable with the most competitive ask $a$ of $A$, $B$
and $A$ are not matchable, which implies $\mathsf{Vol}(M')=0$, and we
are done.

In the second case, when $\mathsf{price}(b) \ge \mathsf{price}(a)$, the
$\mathsf{Match}$ subroutine generates a transaction with transaction
quantity $q = \min (\mathsf{qty}(b),\mathsf{qty}(a))$, before making a
recursive call. Thus, $\mathsf{Vol}(M)\geq q$. It then generates the
remaining set of transactions $\hat M$ by recursively calling
$\mathsf{Match}$ on the reduced order-domain $(\hat B, \hat A)$, which
is obtained from $(B,A)$ by reducing a quantity of $q$ from each of $b$
and $a$, and deleting the zero quantity orders. In particular, at least
one of $b$ and $a$ will be deleted from its respective list, and
$|\hat B|+|\hat A| < |B|+|A|$. Also,
$\mathsf{Vol}(M)=q+\mathsf{Vol}(\hat M)$.

Now, if $\mathsf{Vol}(M')\leq q$ then we are again done as
$\mathsf{Vol}(M)\geq q$. In the case when $\mathsf{Vol}(M') \ge q$, we
invoke Lemma [2](#lem:surgery1){reference-type="ref"
reference="lem:surgery1"} to obtain a uniform matching $M_{ab}$ over
$(B,A)$ such that $\mathsf{Vol}(M')=\mathsf{Vol}(M_{ab})$ and $M_{ab}$
consists of a transaction between $b$ and $a$ with transaction quantity
$q$. To complete the proof, it is sufficient to show

$$\label{eq1} \mathsf{Vol}(M) \ge \mathsf{Vol}(M_{ab}).$$

We now obtain the matching $\hat M_{ab}$ from $M_{ab}$ by deleting the
transaction between $b$ and $a$ (with transaction quantity $q$). Notice
$\hat M_{ab}$ is a matching over $(\hat B,\hat A)$ and

$$\label{eq2} \mathsf{Vol}(M_{ab}) = q + \mathsf{Vol}(\hat M_{ab}).$$

Since $(|\hat B| + |\hat A|) < (|B| + |A|)$, $\hat M$ is over
$(\hat B,\hat A)$, and $\hat M_{ab}$ is a uniform matching over
$(\hat B, \hat A)$, from the induction hypothesis we have

$$\label{eq3} \mathsf{Vol}(\hat M) \ge \mathsf{Vol}(\hat M_{ab}).$$

Combining ([\[eq2\]](#eq2){reference-type="ref" reference="eq2"}) and
([\[eq3\]](#eq3){reference-type="ref" reference="eq3"}), we obtain
([\[eq1\]](#eq1){reference-type="ref" reference="eq1"}):

$$\mathsf{Vol}(M) = q + \mathsf{Vol}(\hat M)) \ge q + \mathsf{Vol}(\hat M_{ab}) = \mathsf{Vol}(M_{ab}).$$ ◻
:::

Having finished this proof, we now turn to the proof of
[2](#lem:surgery1){reference-type="ref" reference="lem:surgery1"} that
we assumed.

::: proof
*Proof of [2](#lem:surgery1){reference-type="ref"
reference="lem:surgery1"}.* Given a uniform matching $M$ with
$\mathsf{Vol}(M) \ge \min\{\mathsf{qty}(b),\mathsf{qty}(a)\}$ over
$(B, A)$, where $b\in B$ and $a\in A$ are the most competitive bid and
ask, respectively, we need to show the existence of a uniform matching
$M_{ab}$ such that $\mathsf{Vol}(M_{ab}) = \mathsf{Vol}(M)$ and $M_{ab}$
contains a transaction between $b$ and $a$ with transaction quantity
$\min\{\mathsf{qty}(b),\mathsf{qty}(a)\}$. Let
$q = \min\{\mathsf{qty}(b),\mathsf{qty}(a)\}$. We do the following
surgery on $M$ in two steps to obtain the desired $M_{ab}$.

Step 1: We first modify $M$ to ensure that bid $b$ and ask $a$ each has
at least $q$ total trade quantities in $M$ (not necessarily between each
other). This is accomplished by running the $\mathsf{Fair}$ procedure on
$M$ that outputs a matching that prefers the most competitive orders
($b$ and $a$) over any other orders. Since $\mathsf{Vol}(M) \ge q$, we
get that $\mathsf{Fair}(M,B,A)$ has at least $q$ trade quantities for
each of $b$ and $a$. Note that $\mathsf{Fair}$ does not change the
volume or affect the uniform properties of $M$. Set
$M \leftarrow \mathsf{Fair}(M,B,A)$.

Step 2: In this step, we modify $M$ to ensure that the bid $b$ and ask
$a$ have $q$ quantity traded between them. Note that in $M$ individually
both $b$ and $a$ have at least $q$ total trade quantities. We will
inductively transfer quantities of $b$ and $a$ that are not between them
to the transaction between $b$ and $a$, a unit quantity at a time, till
they have $q$ quantity trade between them. To better understand this,
consider the case when $b$ and $a$ have zero trade quantity between
them. Let us say there is a transaction between $b$ and $a_1$ of
quantity $q_1$ and a transaction between $a$ and $b_1$ of quantity
$q_2$. We remove these two transactions and replace them with the
following four transactions (see
Figure [2](#fig:surgery){reference-type="ref" reference="fig:surgery"})
that keep the matching volume intact: (1) transaction between $b$ and
$a_1$ of quantity $q_1 -1$, (2) transaction between $a$ and $b_1$ of
quantity $q_2 - 1$, (3) transaction between $b_1$ and $a_1$ of quantity
one and (4) transaction between $b$ and $a$ of quantity one. Recall, in
a uniform matching with price $p$, the limit price of each bid is at
least $p$ and the limit price of each ask is at most $p$, implying any
bid and ask participating in the matching are tradable. Thus, doing such
a replacement surgery is legal and does not affect the uniformity
property, and we obtain the desired $M'$ by repeatedly doing this
surgery. ◻
:::

<figure id="fig:surgery">
<div class="center">
<p><span>!</span></p>
</div>
<figcaption>In the above figure the matching <span
class="math inline"><em>M</em>′</span> is obtained from the matching
<span class="math inline"><em>M</em></span>. Each bid or ask has the
same trade quantity in both <span class="math inline"><em>M</em></span>
and <span class="math inline"><em>M</em>′</span>. Furthermore, the trade
quantity between <span class="math inline"><em>a</em></span> and <span
class="math inline"><em>b</em></span> in <span
class="math inline"><em>M</em>′</span> is one more than that in <span
class="math inline"><em>M</em></span>. </figcaption>
</figure>

Next we prove another important lemma of $\mathsf{Match}$ that will be
useful in establishing the optimality of the maximum matching algorithm
in a subsequent subsection.

::: {#lem:match_optimal_mm .lemma}
**Lemma 3**. *Let $(B, A)$ be an admissible order-domain such that $B$
is sorted by decreasing competitiveness of its bids, whereas, $A$ is
sorted by increasing competitiveness of its asks. Then,
$M = \mathsf{Match}(B, A)$ outputs a maximum volume matching over
$(B, A)$, i.e., for all matchings $M'$ over $(B, A)$,
$\mathsf{Vol}(M) \ge \mathsf{Vol}(M')$.*
:::

In our Coq formalization, this lemma appears as follows.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
Theorem Match_optimal_mm B A:
        admissible B A /\ 
        Sorted bcompetitive B /\ Sorted rev_acompetitive A /\ 
        Matching M B A -> 
        Vol(Match B A) >= Vol(M).
```

Note that this lemma is very similar to
Lemma [3](#lem:match_optimal_mm){reference-type="ref"
reference="lem:match_optimal_mm"} and so is the proof. Hence, like
Lemma [2](#lem:surgery1){reference-type="ref" reference="lem:surgery1"},
we need the following lemma to prove the above result.

::: {#lem:surgery2 .lemma}
**Lemma 4**. *Let the most competitive bid of $B$ be $b$ and the least
competitive ask of $A$ be $a$ such that $b$ and $a$ are tradable. If $M$
is a matching over $(B, A)$ such that
$\mathsf{Vol}(M) \ge \min(\mathsf{qty}(b),\mathsf{qty}(a))$, then there
exists another matching $M_{ab}$ over $(B, A)$ such that
$\mathsf{Vol}(M) = \mathsf{Vol}(M_{ab})$ and $M_{ab}$ contains a
transaction between $b$ and $a$ with quantity
$\min \{\mathsf{qty}(b),\mathsf{qty}(a)\}$.*
:::

We first prove [3](#lem:match_optimal_mm){reference-type="ref"
reference="lem:match_optimal_mm"} assuming
[4](#lem:surgery2){reference-type="ref" reference="lem:surgery2"}, which
is proved subsequently.

::: proof
*Proof idea of Lemma [3](#lem:match_optimal_mm){reference-type="ref"
reference="lem:match_optimal_mm"}.* Let $(B, A)$ be an admissible
order-domain, where $B$ is sorted by decreasing competitiveness of its
bids and $A$ is sorted by increasing competitiveness of its asks. Let
$M=\mathsf{Match}(B,A,\emptyset)$, and let $M'$ be an arbitrary matching
over $(B,A)$. We need to show that
$\mathsf{Vol}(M)\geq\mathsf{Vol}(M')$. We prove this by induction on
$(|B| + |A|)$. In the base case, $B = \emptyset$ or $A = \emptyset$,
which implies $\mathsf{Vol}(M')=0$, and we are trivially done.

Induction step: $|B|\geq 1$ and $|A|\geq 1$. $\mathsf{Match}$ first
removes the top orders $b$ and $a$ from $B$ and $A$, respectively, and
compares their prices. Since both $B$ and $A$ are sorted in decreasing
and increasing orders of their competitiveness, respectively, $b$ is the
most competitive bid of $B$ and $a$ is the least competitive ask of $A$.
We have two cases: $\mathsf{price}(b) < \mathsf{price}(a)$ and
$\mathsf{price}(b) \ge \mathsf{price}(a)$.

In the first case, we have $\mathsf{price}(b) < \mathsf{price}(a)$,
i.e., $b$ and $a$ are not tradable. Since the most competitive bid $b$
is not tradable with $a$, the ask $a$ is not tradable with any bid in
$B$. Therefore, both $M$ and $M'$ are matchings over
$(B,A\setminus\{a\})$. As $|B|+|A\setminus\{a\}|<|B|+|A|$, we are
immediately done by applying the induction hypothesis.

In the second case, when $\mathsf{price}(b) \ge \mathsf{price}(a)$, the
$\mathsf{Match}$ subroutine generates a transaction with transaction
quantity $q = \min (\mathsf{qty}(b),\mathsf{qty}(a))$, before making a
recursive call. Thus, $\mathsf{Vol}(M)\geq q$. It then generates the
remaining set of transactions $\hat M$ by recursively calling
$\mathsf{Match}$ on the reduced order-domain $(\hat B, \hat A)$, which
is obtained from $(B,A)$ by reducing a quantity of $q$ from each of $b$
and $a$, and deleting the zero quantity orders. In particular, at least
one of $b$ and $a$ will be deleted from its respective list, and
$|\hat B|+|\hat A| < |B|+|A|$. Also,
$\mathsf{Vol}(M)=q+\mathsf{Vol}(\hat M)$.

Now, if $\mathsf{Vol}(M')\leq q$ then we are again done as
$\mathsf{Vol}(M)\geq q$. In the case when $\mathsf{Vol}(M') \ge q$, we
invoke Lemma [4](#lem:surgery2){reference-type="ref"
reference="lem:surgery2"} to obtain a matching $M_{ab}$ over $(B,A)$
such that $\mathsf{Vol}(M')=\mathsf{Vol}(M_{ab})$ and $M_{ab}$ consists
of a transaction between $b$ and $a$ with transaction quantity $q$. To
complete the proof, it is sufficient to show

$$\label{eq4} \mathsf{Vol}(M) \ge \mathsf{Vol}(M_{ab}).$$

We now obtain the matching $\hat M_{ab}$ from $M_{ab}$ by deleting the
transaction between $b$ and $a$ (with transaction quantity $q$). Notice
$\hat M_{ab}$ is a matching over $(\hat B,\hat A)$ and

$$\label{eq5} \mathsf{Vol}(M_{ab}) = q + \mathsf{Vol}(\hat M_{ab}).$$

Since $(|\hat B| + |\hat A|) < (|B| + |A|)$, $\hat M$ is over
$(\hat B,\hat A)$, and $\hat M_{ab}$ is a matching over
$(\hat B, \hat A)$, from the induction hypothesis we have

$$\label{eq6} \mathsf{Vol}(\hat M) \ge \mathsf{Vol}(\hat M_{ab}).$$

Combining ([\[eq5\]](#eq5){reference-type="ref" reference="eq5"}) and
([\[eq6\]](#eq6){reference-type="ref" reference="eq6"}), we obtain
([\[eq4\]](#eq4){reference-type="ref" reference="eq4"}):

$$\mathsf{Vol}(M) = q + \mathsf{Vol}(\hat M)) \ge q + \mathsf{Vol}(\hat M_{ab}) = \mathsf{Vol}(M_{ab}).$$ ◻
:::

Having finished this proof, we now discuss the proof of the lemma that
we assumed.

::: proof
*Proof of [4](#lem:surgery2){reference-type="ref"
reference="lem:surgery2"}.* Given a matching $M$ with
$\mathsf{Vol}(M) \ge \min\{\mathsf{qty}(b),\mathsf{qty}(a)\}$ over
$(B, A)$, where $b\in B$ is the most competitive bid and $a\in A$ is the
least competitive ask such that $b$ and $a$ are tradable, we need to
show the existence of a matching $M_{ab}$ such that
$\mathsf{Vol}(M_{ab}) = \mathsf{Vol}(M)$ and $M_{ab}$ contains a
transaction between $b$ and $a$ with transaction quantity
$\min\{\mathsf{qty}(b),\mathsf{qty}(a)\}$. Let
$q = \min\{\mathsf{qty}(b),\mathsf{qty}(a)\}$.

We do the following surgery on $M$ in three steps to obtain the desired
$M_{ab}$.

Step 1: We first modify $M$ to ensure that bid $b$ has at least $q$
total traded quantity in $M$. This is accomplished by running the
$\mathsf{FOB}$ procedure on $M$ that outputs a matching that prefers the
most competitive bid, which is $b$ in our case, over any other bids.
Since $\mathsf{Vol}(M) \ge q$, we get that $\mathsf{FOB}(M,B)$ has at
least $q$ trade quantity of $b$. Note that $\mathsf{FOB}$ does not
change the volume of $M$. Set $M \leftarrow \mathsf{FOB}(M,B)$.

Step 2: In this step, we modify $M$ to ensure that the bid $b$ and ask
$a$ have $q$ quantity traded (not necessarily between them). If
$\mathsf{Qty}(M,\mathsf{id}(a)) < q$, then there exists a transaction
$m$ in $M$ such that bid of $m$ is $b$ and ask of $m$ is not $a$ (since
$\mathsf{Qty}(M,\mathsf{id}(b))\geq q$). We modify $M$ such that we
reduce a single unit from $m$ and increase the trade between $b$ and $a$
by a single unit in $M$. Now the modified matching $M$ has an extra
quantity of $a$ without affecting the Volume of $M$ and the total traded
quantity of $b$ in $M$. We repeat this process until
$\mathsf{Qty}(M,\mathsf{id}(a)) = q$.

Step 3: In this step, we modify $M$ to ensure that $b$ and $a$ have a
transaction with transaction quantity $q$. Since
$Q(M,\mathsf{id}(b))\geq q$ and $Q(M,\mathsf{id}(a))\geq q$, if the the
total traded quantity between $b$ and $a$ is strictly less than $q$,
then there are two transactions $m_1$ between $b$ and $a'$ ($a'\neq a$)
and $m_2$ between $b'$ ($b'\neq b$) and $a$ in $M$. We reduce the
transaction quantities of $m_1$ and $m_2$ by a single unit each. Next,
we increase the transaction quantity of the transaction between $b$ and
$a$ by a single unit. Finally, we increase the transaction quantity of
the transaction between $b'$ and $a'$ by a single unit; note $b'$ and
$a'$ must be tradable, as $b'$ was traded with $a$, the least
competitive ask, so $b'$ is tradable with all asks. Note that this step
does not alter $\mathsf{Vol}(M)$, $\mathsf{Qty}(M, \mathsf{id}(b))$, and
$\mathsf{Qty}(M,\mathsf{id}(a)$, but increases the transaction quantity
between $b$ and $a$. We repeatedly apply this surgery to obtain the
desired matching. ◻
:::

## Optimal-Uniform Matching Algorithm {#sec:uniform}

In this section, we describe the $\mathsf{UM}$ process that takes as
input a list of bids and a list of asks and produces a fair and optimal
uniform matching that can be directly used in the financial markets for
conducting call auctions. We present a proof of correctness of the
$\mathsf{UM}$ process.

::: algorithm
::: algorithmic
Sort the bids in $B$ in decreasing order of competitiveness. Sort the
asks in $A$ in decreasing order of competitiveness.
$M = \mathsf{Match}(B,A,\emptyset)$
$p = \mathsf{Last\_Transaction\_Price}(M)$
$\mathsf{Assign\_Transaction\_Price}(p, M)$
:::
:::

Given the lists of bids and asks, $B$ and $A$, $\mathsf{UM}$ first sorts
them (by decreasing competitiveness). It then invokes $\mathsf{Match}$
on the sorted lists $B$, $A$, and the empty matching $\emptyset$, which
outputs a matching $M$. Note that the transaction price assigned by
$\mathsf{Match}$ to each matched bid-ask pair is the price of the ask in
that pair, and hence the matching output by $\mathsf{Match}$ need not be
uniform.[^4] To produce a uniform matching we have to assign a single
transaction price to all the transactions of $M$ which we choose to be
the transaction price, $p$, of the last matched bid-ask pair, $(b',a')$,
of $M$. This is done by the $\mathsf{Assign\_Transaction\_Price}$
subroutine and it does not affect the transaction quantities of $M$;
thus, the volume of $M$ is not affected. We now explain why this
assignment does not violate the matching property of $M$. Let the
participating bids of $M$ be $B'\subseteq B$ and participating asks of
$M$ be $A'\subseteq A$. Recall that before assigning the uniform
transaction price $M$ is a matching from
[2](#lem:match_matching){reference-type="ref"
reference="lem:match_matching"}. Since $\mathsf{Match}$ scans the sorted
lists $B$ and $A$ in decreasing competitiveness,
$\mathsf{price}(a')\geq\mathsf{price}(a)$ for all $a\in A'$ and
$\mathsf{price}(b')\leq \mathsf{price}(b)$ for all $b\in B'$. Since,
$\mathsf{price}(a')\leq p \leq \mathsf{price}(b')$, we have for all
$a\in A'$ and $b\in B'$
$\mathsf{price}(a)\leq\mathsf{price}(a')\leq p\leq\mathsf{price}(b')\leq\mathsf{price}(b)$.
Hence, $p$ will not violate the limit prices of any of the matched
bid-ask pairs. Thus, $\mathsf{UM}$ outputs a uniform matching.

Next, from
[\[lem:match_foa,lem:match_fob\]](#lem:match_foa,lem:match_fob){reference-type="ref"
reference="lem:match_foa,lem:match_fob"} $\mathsf{Match}$ outputs a fair
matching since both $B$ and $A$ are sorted. Notice that the fairness
property is not affected by updating the transaction prices of a
matching. Thus, $M$ remains a fair matching after uniform price
assignment. Finally, from
[1](#lem:match_optimal_um){reference-type="ref"
reference="lem:match_optimal_um"}, we conclude that $\mathsf{UM}$
outputs a maximum volume uniform matching. Combining all these
observations, we obtain our main result for $\mathsf{UM}$.

In our Coq formalization, this theorem appears as follows.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* The UM is fair and optimal uniform algorithm. *)
Theorem UM_correct B A:
        admissible B A -> 
        Is_fair (UM B A) B A /\ Is_optimal_uniform (UM B A) B A.
```

## Maximum Matching Algorithm {#sec:maximum}

In this section, we describe the $\mathsf{MM}$ process that takes as
input a list of bids $B$ and a list of asks $A$ and produces a maximum
volume matching over $(B,A)$. We present a proof of correctness of the
$\mathsf{MM}$ process.

::: algorithm
::: algorithmic
Sort the bids in $B$ in decreasing order of competitiveness. Sort the
asks in $A$ in increasing order of competitiveness.
$M = \mathsf{Match}(B,A,\emptyset)$ $M' = \mathsf{FOA}(M,A)$ $M'$
:::
:::

$\mathsf{MM}$ first sorts the list $B$ in decreasing order of
competitiveness and list $A$ in increasing order of competitiveness,
i.e., the most competitive bid is at the top of $B$ and the least
competitive ask is at the top of $A$. It then invokes $\mathsf{Match}$
on the lists $B$, $A$, and the empty matching $\emptyset$, which outputs
the matching $M$. Finally, it invokes the $\mathsf{FOA}$ algorithm with
$M$ and $A$ as the input, to obtain $M'$, which is then returned. We
argue that $M'$ is a maximum matching over $(B,A)$.

From [2](#lem:match_matching){reference-type="ref"
reference="lem:match_matching"}, the $\mathsf{Match}$ algorithm outputs
a matching. From [3](#lem:match_fob){reference-type="ref"
reference="lem:match_fob"} $\mathsf{Match}$ outputs a fair on bids
matching since $B$ is sorted in decreasing order of competitiveness.
Also, from [1](#thm:FOA){reference-type="ref" reference="thm:FOA"}, the
output $M'$ of $\mathsf{FOA}(M,A)$ is a fair matching. Finally, from
[3](#lem:match_optimal_mm){reference-type="ref"
reference="lem:match_optimal_mm"}, $M'$ is a maximum volume matching.
Thus, our main result for $\mathsf{MM}$ can be stated as follows.

In our Coq formalization, this theorem appears as follows.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* The MM is fair and maximum volume matching algorithm. *)
Theorem MM_correct B A:
        admissible B A -> 
        Is_maximum (MM B A) B A /\ Is_fair (MM B A) B A.
```

Formalization notes: First we define the 'Match' function and prove all
of its properties in the 'Match.v' file. The $\mathsf{UM}$ process and
its correctness proof are written in the 'UM.v' file. Similarly,
$\mathsf{MM}$ process and its correctness proof are written in the
'MM.v' file.

# Uniqueness Theorems and Automated Checkers {#sec:uniqueness}

In this section, we establish certain theorems that enable us to
automatically check for violations in an exchange matching algorithm by
comparing its output with the output of our certified program. Detailed
proofs are available in the Coq formalization [@git:call].

Ideally, we would have wanted a theorem that states that the properties
(fair and optimal uniform) imply a unique matching. Such a theorem would
enable us to automatically compare a matching produced by an exchange
with a matching produced by our certified program to find violations of
these properties in the matching produced by the exchange.
Unfortunately, such a theorem is not possible; there exists two
different matchings $M_1$ and $M_2$ over the same admissible
order-domain both of which are fair and optimal uniform:
$M_1 = \{(b_1,a_1,1,p), (b_2,a_2,2,p)\}$ and
$M_2 = \{(b_1,a_2,1,p), (b_2,a_2,1,p), (b_2,a_1,1,p)\}$ on bids
$B = \{(b_1,* , 1, p),  (b_2, *, 2, p)\}$ and asks
$A = \{(a_1,*,  1, p),  (a_2,*, 2, p)\}$ for some arbitrary price $p$
and timestamps (which are not made explicit; instead we use $*$ as a
placeholder). Observe that $M_1$ and $M_2$ are both uniform (since
transaction prices are all $p$), fair (since all orders are fully traded
in both $M_1$ and $M_2$), with volume $3$ (which is the maximum possible
volume as $\mathsf{Vol}(B) = 3$). Note that fairness does not require
the most competitive bid to be paired with the most competitive ask. For
example, assuming $a_1$ has a lower timestamp than $a_2$ and $b_1$ has a
lower timestamp than $b_2$ in the above example, $a_1$ and $b_1$ are not
matched in the matching $M_2$, which is a fair matching. Nonetheless, we
can show that given an admissible order-domain, all matchings that are
fair and uniform must have the same trade volume for each order. This
still allows us to automatically check for violations of the properties
in an exchange, by comparing the trades of each order produced by the
exchange against that produced by our certified program.

We have the following theorem which formulates this uniqueness relation
on the matchings.

This theorem appears in our Coq formalization as

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* Uniqueness preperty (completeness) *)
Theorem completeness M1 M2 B A:
        admissible B A /\ (Vol(M1) = Vol(M2)) /\
        (Matching M1 B A) /\ (Matching M2 B A) /\
        Is_fair M1 B A /\ Is_fair M2 B A ->

        (forall a, Qty_ask M1 (id a) = Qty_ask M2 (id a)) /\
        (forall b, Qty_bid M1 (id b) = Qty_bid M2 (id b)).
```

Observe that if we specify that an algorithm must output a fair and a
maximum volume matching, the output is "unique" in the sense that each
order in the input will have the same quantity traded in the output
matching. Similarly, uniqueness holds when we specify that the algorithm
must output a fair and an optimal uniform matching. The only freedom
that the algorithm has is in deciding which bid gets traded with which
ask, their trade quantity, and the transaction price. For uniform price
matching, which is predominantly used in the opening sessions of various
stock markets for price discovery, in fact, who gets traded with whom
also becomes practically irrelevant, as all participants are matched at
the same price. Thus, roughly speaking, these requirements form an
almost complete specification for the problem.

From the above theorem, the following corollaries are immediate.

::: {#thm:uniquenessTheorem2 .corollary}
**Corollary 1**. *For any two fair and maximum matchings $M_1$ and $M_2$
over an admissible order-domain $(B, A)$, for each order $\omega$, the
total traded quantity of $\omega$ in $M_1$ is equal to the total traded
quantity of $\omega$ in $M_2$.*
:::

::: {#thm:uniquenessTheorem3 .corollary}
**Corollary 2**. *For any two fair and optimal uniform matchings $M_1$
and $M_2$ over an admissible order domain $(B, A)$, for each order
$\omega$, the total traded quantity of $\omega$ in $M_1$ is equal to the
total traded quantity of $\omega$ in $M_2$.*
:::

For optimal uniform matching, for each order, we can compare the total
traded quantities of the order in the matching $M_1$ produced by an
exchange with the total traded quantities of the order in the matching
$M_2=\mathsf{UM}(B, A)$ produced by our certified program. If for some
order, the traded quantities do not match, then from
[\[thm:UMcorrect\]](#thm:UMcorrect){reference-type="ref"
reference="thm:UMcorrect"} and
[2](#thm:uniquenessTheorem3){reference-type="ref"
reference="thm:uniquenessTheorem3"} we know that $M_1$ does not have the
desired properties as required by the regulators. On the other hand, if
they do match for all orders, then the following theorem gives the
guarantee that $M_1$ is fair (note that the uniform property can be
verified directly from the transaction prices and clearly the total
trade volume of $M_1$ and $M_2$ are the same if the traded quantities
are the same for each order).

The above theorem appears in our Coq formalization as follows.

``` {.coq bgcolor="gray!05" fontsize="\\scriptsize"}
(* Converse uniqueness preperty *)
Theorem soundness M1 M2 B A:
        admissible B A /\ 
        (Matching M1 B A) /\ (Matching M2 B A) /\
        Is_fair M2 B A /\ (Vol(M1) = Vol(M2)) /\
        (forall a, Qty_ask M1 (id a) = Qty_ask M2 (id a)) /\
        (forall b, Qty_bid M1 (id b) = Qty_bid M2 (id b)) -> 

        Is_fair M1 B A.
```

We now provide the proofs of these theorems.

::: proof
*Proof of
[\[thm:uniquenessTheorem\]](#thm:uniquenessTheorem){reference-type="ref"
reference="thm:uniquenessTheorem"}.* We will prove by contradiction
using the following property of a matching
$$\label{eq7} \mathsf{Vol}(M) = \sum_{b \in B}\mathsf{Qty}(M, \mathsf{id}(b)).$$

Let $M_1$ and $M_2$ be fair matchings such that
$\mathsf{Vol}(M_1) = \mathsf{Vol}(M_2)$. Let $b$ be a bid whose total
trade quantity in $M_1$ is different (without loss of generality, more)
from its total trade quantity in $M_2$. It is easy to show that there
exists another bid $b'$ such that its total traded quantity in $M_1$ is
less than her total traded quantity in $M_2$, i.e.,
$\mathsf{Qty}(M_2, \mathsf{id}(b')) > \mathsf{Qty}(M_1, \mathsf{id}(b'))$
(since the sum of the total traded quantities of all the bids of $B$ in
$M_1$ is equal to the sum of the total traded quantities of all the bids
of $B$ in $M_2$ from [\[eq7\]](#eq7){reference-type="ref"
reference="eq7"}.

Now, there can be two cases: (i) $b$ is more competitive than $b'$ or
(ii) $b'$ is more competitive than $b$. In the first case, since
$\mathsf{Qty}(M_1, \mathsf{id}(b)) > \mathsf{Qty}(M_2, \mathsf{id}(b))$,
it follows that
$\mathsf{Qty}(M_2, \mathsf{id}(b)) < \mathsf{Qty}(M_1, \mathsf{id}(b)) \leq \mathsf{qty}(b)$;
in particular, in the matching $M_2$, $b$ is not fully traded. But,
since $\mathsf{Qty}(M_2, \mathsf{id}(b'))$
$> \mathsf{Qty}(M_1, \mathsf{id}(b')) \ge 0$, we have that $b'$ gets
traded in $M_2$. This contradicts the fact that $M_2$ is fair on the
bids as a less competitive bid $b'$ is being traded in $M_2$, while a
more competitive bid $b$ is not fully traded. Similarly, in the second
case, we can derive a contradiction to the fact that the matching $M_1$
is fair on the bids. ◻
:::

The proof of
[\[thm:ConverseUniquenessTheorem\]](#thm:ConverseUniquenessTheorem){reference-type="ref"
reference="thm:ConverseUniquenessTheorem"} follows immediately from the
definition of fairness.

Formalization notes: All the theorems in this section are formalized in
the file 'Uniqueness.v' using the above proof ideas.

## Demonstration: Automatic Detection of Violations {#sec:demonstration}

In this section, we demonstrate the practical applicability of our work.
For this, we procured real data from a prominent stock exchange. This
data consists of order-book and trade-book of everyday trading for a
certain number of days. For our demonstration, we considered trades for
the top 100 stocks (as per their market capitalization) of a particular
day. For privacy reasons, we conceal the real identity of the traders,
stocks and the exchange by masking the stock names (to s1 to s100) and
the traders' identities. We also converted the timestamps appropriately
into natural numbers (which keeps the time in microseconds, as in the
original data). Furthermore, the original data has multiple requests
with the same order id; this is because some traders update or delete an
existing order placed by them before the call auction is conducted.
After our preprocessing, we just have the final lists of bids and asks
in the order-book that participate in the auction. Furthermore, there
are certain market orders, i.e., orders that are ready to be traded at
any available price, which effectively means a limit price of zero for
an ask and a limit price of infinity for a bid; in the preprocessing, we
set these limit prices to zero and the largest OCaml integer,
respectively.

We then extracted the verified OCaml programs and ran them on the
processed market data. The output trades of the verified code were then
compared with the actual trades in the trade-book from the exchange.
From the uniqueness theorems in
[6](#sec:uniqueness){reference-type="ref" reference="sec:uniqueness"},
we know that if the total trade quantity of each order in these two
matchings are equal, then the matching produced by the exchange has the
desired properties (whether it is uniform or not, can be checked
trivially by looking at the prices in the trade-book). We also know that
if they are not equal for some traders, then the matching algorithm of
the exchange does not have the requisite desired properties (or there is
some error in storing or reporting the order-book or the trade-book
accurately).

The processed data and the relevant programs for this demonstration are
available at  [@git:call]. The extracted OCaml programs of the functions
required for this demonstration are stored in a separate file named
'certified.ml'. The input bids, asks, and trades of each stock are in
's.bid', 's.ask', and 's.trade' files, respectively, where 's' is the
masked id for that stock. For example, file 's1.bid' contains all the
bids for the stock 's1'. Our automated checker additionally uses two
OCaml scripts: create.ml and compare.ml. The create.ml script feeds
inputs (lists of bids and asks) to the UM process, and then prints its
output matching $M$. The compare.ml script compares the matching
produced by the UM process $M$ with the actual trades $M_\text{EX}$ in
the exchange trade-book. If the total trade quantity for all the traders
in $M$ matches with that of the total trade quantity in $M_\text{EX}$,
then the compare.ml script outputs \"Matching does not violate the
guidelines\". If for some bid (or ask) the total trade quantity of $M$
and $M_\text{EX}$ does not match, then the program outputs \"Violation
detected!\".

Out of the 100 stocks we checked, for three stocks our program outputted
\"Violation detected!\". When we closely examined these stocks, we
realized that in all of these stocks, a market ask order (with limit
price = 0), was not matched by the exchange in its trading output (and
these were the only market ask orders in the entire order-book). On the
contrary, market bid orders were matched by them. With further
investigation, we observed that corresponding to each of these three
violations, in the raw data there was an entry of update request in the
order-book with a limit price and timestamp identical to the uniform
price and the auction time, respectively. It seems highly unlikely that
these three update requests were placed by the traders themselves (to
match the microsecond time and also the trade price seems very
improbable); we suspect this is an exchange's system generated entry in
the order-book. We hope that the exchange is aware of this and doing
this consciously. When we delete the market asks in the preprocessing
stage, no violations are detected. Even if it is not a violation (but a
result of the exchange implementing some unnatural rule that we are not
aware of), it is fascinating to see that with the help of verified
programs, we can identify such minute and interesting anomalies that can
be helpful for regulating and improving the exchange's matching
algorithm.

[^1]: An earlier version of this work appeared in ITP [@RSS21].

[^2]: Observe that any value in the interval of the limit prices of the
    matched bid-ask pair can be assigned as the transaction price.

[^3]: A symmetric version of $\mathsf{Match}$ can be used as well, where
    if $b$ and $a$ are not tradable, $b$ is deleted.

[^4]: Observe that any value in the interval of the limit prices of the
    matched bid-ask pair can be assigned as the transaction price and it
    will not affect any analysis done in this work.
