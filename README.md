# redex-into-coq
Source code of Redex->Coq.

This is the source code of Redex -> Coq: a tool to automate the
translation of Redex models into a (hopefully) semantically equivalent model in Coq,
and to provide tactics to help in the certification of fundamental properties of such models.
The work is heavily based on a model of Redex's semantics developed by 
Klein et al. [1]. 

The tool is in an early stage of development. The accompanying paper that describes the features present in this version is [2].
We present a brief description of each file present in the mechanization, together with a reference to the corresponding section in [2]:

+ patterns_terms.v     : implementation of the languages of patterns and terms, together with several tools to reason over them (section 3.1).
+ patterns_terms_dec.v : decidability results about the languages of patterns and terms (section 3.1.5).
+ match_tads.v         : data-structures used to represent the results returned by the matching algorithm (sections 3.1.7 and 3.2.6).
+ grammar.v            : module type "Grammar" and an instantiation of it as a regular grammar, using Coq's lists (section 3.1.6).
+ wf_rel.v             : well-founded relation over the domain of the matching function (section 3.2.1).
+ match_impl.v         : the actual implementation of the matching algorithm (section 3.2.6).
+ match_spec_orig.v    : a mechanization of the original formal system from [1], that specifies matching and decomposition (it is a modified version of what is presented in (sections 3.2.4 and 3.2.5; also see section 4).
+ reduction.v          : mechanization of the semantics of context-sensitive reduction rules (section 3.2.7).
+ verification         : folder containing modules containing the several soundness results obtained, described below.

The content of the verification folder includes:
+ match_spec.v                   : a modification of the formal system present in match_spec_orig.v, suitable for verification purposes of the implemented matching algorithm (sections 3.2.4 and 3.2.5).
+ match_impl_lemmas.v            : a collection of results about the implemented matching algorithm, to be used when proving soundness and completeness.
+ match_spec_lemmas.v            : results about our modified formal system that specifies matching and decomposition (section 4).
+ match_spec_equiv.v             : mechanical proofs of correspondence between the original specifications of matching/decomposition and our modified versions (section 4).
+ completeness.v and soundness.v : mechanized proofs of completeness and soundness of the matching/decomposition algorithm, respectively, with respect to its specification (section 4).

In folder "examples/cbv" we offer a mechanization of a call-by-value lambda-calculus with normal-order reduction. It serves mainly to showcase the actual capabilities of Redex that are mechanized in the present version of the tool, and how to invoke them to implement a reduction-semantics model:
+ cbv_grammar.v        : defines the language of lambda-terms.
+ cbv_sem.v            : implements a call-by-value beta-contraction.
+ cbv_meta_functions.v : implements capture-avoiding substitution and defines the notion of "free-variables" in lambda-terms.
+ cbv_tests.v          : implements several simple tests cases to illustrates the capabilities of the model.

Note that, in the present early state of the tool, the performance of matching/decomposition impedes testing with more interesting examples. Future iterations of the tool should improve performance, usability and capabilities of the tool.

 
[2] "Redex $\rightarrow$ Coq: towards a theory of decidability of Redex's reduction semantics"
