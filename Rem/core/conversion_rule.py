'''

See (https://coq.inria.fr/refman/language/core/conversion.html)

'''


from __future__ import annotations

from .context import *
from .environment import *
from .typing_rule import MP_WF, MP_WT

from ..metaproof import MetaProof


# alpha-conversion judgement is implemented in `Term`.
    

class MP_reduction(MetaProof):
    '''
    reduction relation: `E[Γ] ⊢ t1 ▷ t2`.

    Note: the reduction rule here also considers alpha-convertibility.
    '''
    def __init__(self, E : Environment, Gamma : Context, t1 : Term, t2 : Term):
        CIC_SYS_type_check(E, Environment)
        CIC_SYS_type_check(Gamma, Context)
        CIC_SYS_type_check(t1, Term)
        CIC_SYS_type_check(t2, Term)

        self.__E = E
        self.__Gamma = Gamma
        self.__t1 = t1
        self.__t2 = t2

    @property
    def E(self) -> Environment:
        return self.__E
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma
    
    @property
    def t1(self) -> Term:
        return self.__t1

    @property
    def t2(self) -> Term:
        return self.__t2

    def conclusion(self) -> str:
        return f"{self.E}{self.Gamma} ⊢ {self.t1} ▷ {self.t2}"
    
class MP_reduction_trans(MP_reduction):
    '''
    The transitivity construction of reduction relation.
    ```
        E[Γ] ⊢ t1 ▷ t2
        E[Γ] ⊢ t2 ▷ t3
        -----------------
        E[Γ] ⊢ t1 ▷ t3
    ```
    '''
    rule_name = "reduct-trans"
    def __init__(self, red1 : MP_reduction, red2 : MP_reduction):

        # proof of `E[Γ] ⊢ t1 ▷ t2`
        CIC_SYS_type_check(red1, MP_reduction)

        # proof of `E[Γ] ⊢ t2 ▷ t3`
        CIC_SYS_type_check(red2, MP_reduction)

        # consistent 'E'
        if not red1.E == red2.E:
            raise CIC_SYS_Error("Inconsistent environment.")
        
        # consistent 'Γ'
        if not red1.Gamma == red2.Gamma:
            raise CIC_SYS_Error("Inconsistent context.")
        
        # consistent 't2'
        if not red1.t2 == red2.t1:
            raise CIC_SYS_Error("Inconsistent intermediate term.")
        
        self.__red1 = red1
        self.__red2 = red2

        # the conclusion `E[Γ] ⊢ t1 ▷ t3`
        super().__init__(red1.E, red1.Gamma, red1.t1, red2.t2)

    def premises(self) -> str:
        res = self.__red1.conclusion() + "\n"
        res += self.__red2.conclusion() + "\n"
        return res


class MP_beta_reduction(MP_reduction):
    '''
    β-reduction
    ```
        -----------------------------
        E[Γ] ⊢ ((λx:T.t) u) ▷ t{x/u}
    ```
    '''
    rule_name = "β-reduction"

    def __init__(self, E : Environment, Gamma : Context, t1 : Apply, t2 : Term):

        # check `((λx:T.t) u)`
        CIC_SYS_type_check(t1, Apply)
        CIC_SYS_type_check(t1.t, Abstract)
        assert(isinstance(t1.t, Abstract))

        # check `t2`
        t2_sub = t2.substitute(t1.t.x, t1.u)
        if not t2_sub.alpha_convertible(t2):
            raise CIC_SYS_Error(f"beta-reduction: the substitution result '{t2_sub}' is not alpha-convertible to '{t2}'.")
        
        # the conclusion `E[Γ] ⊢ ((λx:T.t) u) ▷ t{x/u}`
        super().__init__(E, Gamma, t1, t2)

    def premises(self) -> str:
        return ""

        
class MP_delta_reduction(MP_reduction):
    '''
    δ-reduction
    ```
        WF(E)[Γ]
        (x:=t:T) ∈ Γ
        -----------------------------
        E[Γ] ⊢ x ▷ t
    ```
    '''
    rule_name = "δ-reduction"

    def __init__(self, wf : MP_WF, x_in_Gamma : MP_Cont_Contain_Def):

        # proof of `WF(E)[Γ]`
        CIC_SYS_type_check(wf, MP_WF)

        # proof of `(x:=t:T) ∈ Γ`
        CIC_SYS_type_check(x_in_Gamma, MP_Cont_Contain_Def)

        # consistent 'Γ'
        if not wf.Gamma == x_in_Gamma.Gamma:
            raise CIC_SYS_Error("Inconsistent contexts.")
        
        self.__wf = wf
        self.__x_in_Gamma = x_in_Gamma

        # the conclusion `E[Γ] ⊢ x ▷ t`
        super().__init__(wf.E, wf.Gamma, x_in_Gamma.var_def.x, x_in_Gamma.var_def.t)

    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__x_in_Gamma.conclusion() + "\n"
        return res
    

class MP_Delta_reduction(MP_reduction):
    '''
    Δ-reduction
    ```
        WF(E)[Γ]
        (c:=t:T) ∈ E
        -----------------------------
        E[Γ] ⊢ c ▷ t
    ```
    '''
    rule_name = "Δ-reduction"

    def __init__(self, wf : MP_WF, c_in_E : MP_Env_Contain_Def):

        # proof of `WF(E)[Γ]`
        CIC_SYS_type_check(wf, MP_WF)

        # proof of `(c:=t:T) ∈ E`
        CIC_SYS_type_check(c_in_E, MP_Env_Contain_Def)

        # consistent 'E'
        if not wf.E == c_in_E.E:
            raise CIC_SYS_Error("Inconsistent environment.")
        
        self.__wf = wf
        self.__c_in_E = c_in_E

        # the conclusion `E[Γ] ⊢ x ▷ t`
        super().__init__(wf.E, wf.Gamma, c_in_E.const_def.c, c_in_E.const_def.t)

    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__c_in_E.conclusion() + "\n"
        return res
    

# ι-reduction is omitted here.

class MP_zeta_reduction(MP_reduction):
    '''
    ζ-reduction
    ```
        WF(E)[Γ]
        E[Γ] ⊢ u : U
        E[Γ::(x:=u:U)] ⊢ t : T
        ------------------------------------
        E[Γ] ⊢ let x := u : U in t ▷ t{x/u}
    ```
    '''
    rule_name = "ζ-reduction"

    def __init__(self, wf : MP_WF, wt_outer : MP_WT, wt_inner : MP_WT):

        # proof of `WF(E)[Γ]`
        CIC_SYS_type_check(wf, MP_WF)

        # proof of `E[Γ] ⊢ u : U`
        CIC_SYS_type_check(wt_outer, MP_WT)

        # proof of `E[Γ::(x:=u:U)] ⊢ t : T`
        CIC_SYS_type_check(wt_inner, MP_WT)

        # consistent 'E'
        if wf.E != wt_outer.E or wf.E != wt_inner.E:
            raise CIC_SYS_Error("Inconsistent environment.")
        
        # break `Γ::(x:=u:U)`
        Gamma_pre, dec = wt_inner.Gamma.pop()
        if not isinstance(dec, LocalDef):
            raise CIC_SYS_Error("Invalid inner context.")

        # consistent 'Γ'
        if wf.Gamma != wt_outer.Gamma or wf.Gamma != Gamma_pre:
            raise CIC_SYS_Error("Inconsistent context.")
        
        # consistent 'u'
        if not wt_outer.t == dec.t:
            raise CIC_SYS_Error("Inconsistent 'u'.")
        
        # consistent 'U'
        if not wt_outer.T == dec.T:
            raise CIC_SYS_Error("Inconsistent 'U'.")
        
        self.__wf = wf
        self.__wt_outer = wt_outer
        self.__wt_inner = wt_inner

        # the conclusion `E[Γ] ⊢ let x := u : U in t ▷ t{x/u}`
        t1 = Let_in(dec.x, dec.t, dec.T, wt_inner.t)
        t2 = wt_inner.t.substitute(dec.x, wt_outer.t)
        super().__init__(wf.E, wf.Gamma, t1, t2)

    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__wt_outer.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

class MP_eta_expansion(MetaProof):
    '''
    η-expansion

    It is legal to identify any term `t` of functional type `∀x:T, U` with its so-called η-expansion `λx:T.(t x)`.

    ```
        E[Γ] ⊢ t : ∀x:T, U
        -------------------
        t ~η λx:T.(t x)
    ```
    '''
    rule_name = "η-expansion"

    def __init__(self, wt : MP_WT, expansion : Abstract):
        '''
        Note: it checks whether the well-typed term `t` in `wt` can be expand to `expansion`.
        '''
        # proof of `E[Γ] ⊢ t : ∀x:T, U`
        CIC_SYS_type_check(wt, MP_WT)
        if not isinstance(wt.T, Prod):
            raise CIC_SYS_Error(f"Invalid term for η-expansion: '{wt}' is not a term of product.")

        # check the expansion relation
        fresh_var = Var.fresh_var((wt.t, wt.T))
        expansion_calc = Abstract(fresh_var, wt.T.T, Apply(wt.t, fresh_var))
        if not expansion_calc == expansion:
            raise CIC_SYS_Error("Inconsistent expansion term.")
        
        self.__wt = wt
        self.__expansion = expansion

    def premises(self) -> str:
        return self.__wt.conclusion()
    
    def conclusion(self) -> str:
        return f"{self.__wt.t} ~η {self.__expansion}"