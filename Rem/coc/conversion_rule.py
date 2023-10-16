'''

See (https://coq.inria.fr/refman/language/core/conversion.html)

'''


from __future__ import annotations

from .context import *
from .environment import *
from .typing_rule import MP_WF, MP_WT

from ..metadef import MetaProof


# alpha-conversion judgement is implemented in `Term`.
    
@meta_term
class MP_reduction(MetaProof):
    '''
    reduce
    ```
        E[Γ] ⊢ t1 ▷ t2
    ```

    Note: the reduction rule here also considers alpha-convertibility.
    '''
    def __init__(self, E : Environment, Gamma : Context, t1 : Term, t2 : Term):
        Meta_Sys_type_check(E, Environment)
        Meta_Sys_type_check(Gamma, Context)
        Meta_Sys_type_check(t1, Term)
        Meta_Sys_type_check(t2, Term)

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
    

@concrete_term
class MP_reduction_trans(MP_reduction):
    '''
    reduce-trans
    ```
        E[Γ] ⊢ t1 ▷ t2
        E[Γ] ⊢ t2 ▷ t3
        -----------------
        E[Γ] ⊢ t1 ▷ t3
    ```

    The transitivity construction of reduction relation.
    '''
    
    def __init__(self, red1 : MP_reduction, red2 : MP_reduction):

        # proof of `E[Γ] ⊢ t1 ▷ t2`
        Meta_Sys_type_check(red1, MP_reduction)

        # proof of `E[Γ] ⊢ t2 ▷ t3`
        Meta_Sys_type_check(red2, MP_reduction)

        # consistent 'E'
        if not red1.E == red2.E:
            raise Meta_Sys_Error("Inconsistent environment.")
        
        # consistent 'Γ'
        if not red1.Gamma == red2.Gamma:
            raise Meta_Sys_Error("Inconsistent context.")
        
        # consistent 't2'
        if not red1.t2 == red2.t1:
            raise Meta_Sys_Error("Inconsistent intermediate term.")
        
        self.__red1 = red1
        self.__red2 = red2

        # the conclusion `E[Γ] ⊢ t1 ▷ t3`
        super().__init__(red1.E, red1.Gamma, red1.t1, red2.t2)

    def premises(self) -> str:
        res = self.__red1.conclusion() + "\n"
        res += self.__red2.conclusion() + "\n"
        return res

@concrete_term
class MP_beta_reduction(MP_reduction):
    '''
    β-reduction
    ```
        -----------------------------
        E[Γ] ⊢ ((λx:T.t) u) ▷ t{x/u}
    ```
    '''
    

    def __init__(self, E : Environment, Gamma : Context, t1 : Apply, t2 : Term):

        # check `((λx:T.t) u)`
        Meta_Sys_type_check(t1, Apply)
        Meta_Sys_type_check(t1.t, Abstract)
        assert(isinstance(t1.t, Abstract))

        # check `t2`
        t2_sub = t2.substitute(t1.t.x, t1.u)
        if not t2_sub.alpha_convertible(t2):
            raise Meta_Sys_Error(f"beta-reduction: the substitution result '{t2_sub}' is not alpha-convertible to '{t2}'.")
        
        # the conclusion `E[Γ] ⊢ ((λx:T.t) u) ▷ t{x/u}`
        super().__init__(E, Gamma, t1, t2)

    def premises(self) -> str:
        return ""


@concrete_term
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

    def __init__(self, wf : MP_WF, x_in_Gamma : MP_Cont_Contain_Def):

        # proof of `WF(E)[Γ]`
        Meta_Sys_type_check(wf, MP_WF)

        # proof of `(x:=t:T) ∈ Γ`
        Meta_Sys_type_check(x_in_Gamma, MP_Cont_Contain_Def)

        # consistent 'Γ'
        if not wf.Gamma == x_in_Gamma.Gamma:
            raise Meta_Sys_Error("Inconsistent contexts.")
        
        self.__wf = wf
        self.__x_in_Gamma = x_in_Gamma

        # the conclusion `E[Γ] ⊢ x ▷ t`
        super().__init__(wf.E, wf.Gamma, x_in_Gamma.var_def.x, x_in_Gamma.var_def.t)

    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__x_in_Gamma.conclusion() + "\n"
        return res
    

@concrete_term
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

    def __init__(self, wf : MP_WF, c_in_E : MP_Env_Contain_Def):

        # proof of `WF(E)[Γ]`
        Meta_Sys_type_check(wf, MP_WF)

        # proof of `(c:=t:T) ∈ E`
        Meta_Sys_type_check(c_in_E, MP_Env_Contain_Def)

        # consistent 'E'
        if not wf.E == c_in_E.E:
            raise Meta_Sys_Error("Inconsistent environment.")
        
        self.__wf = wf
        self.__c_in_E = c_in_E

        # the conclusion `E[Γ] ⊢ x ▷ t`
        super().__init__(wf.E, wf.Gamma, c_in_E.const_def.c, c_in_E.const_def.t)

    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__c_in_E.conclusion() + "\n"
        return res
    

# ι-reduction is omitted here.


@concrete_term
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

    def __init__(self, wf : MP_WF, wt_outer : MP_WT, wt_inner : MP_WT):

        # proof of `WF(E)[Γ]`
        Meta_Sys_type_check(wf, MP_WF)

        # proof of `E[Γ] ⊢ u : U`
        Meta_Sys_type_check(wt_outer, MP_WT)

        # proof of `E[Γ::(x:=u:U)] ⊢ t : T`
        Meta_Sys_type_check(wt_inner, MP_WT)

        # consistent 'E'
        if wf.E != wt_outer.E or wf.E != wt_inner.E:
            raise Meta_Sys_Error("Inconsistent environment.")
        
        # break `Γ::(x:=u:U)`
        Gamma_pre, dec = wt_inner.Gamma.pop()
        if not isinstance(dec, LocalDef):
            raise Meta_Sys_Error("Invalid inner context.")

        # consistent 'Γ'
        if wf.Gamma != wt_outer.Gamma or wf.Gamma != Gamma_pre:
            raise Meta_Sys_Error("Inconsistent context.")
        
        # consistent 'u'
        if not wt_outer.t == dec.t:
            raise Meta_Sys_Error("Inconsistent 'u'.")
        
        # consistent 'U'
        if not wt_outer.T == dec.T:
            raise Meta_Sys_Error("Inconsistent 'U'.")
        
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
    

@concrete_term
class MP_eta_conversion(MetaProof):
    '''
    η-expansion (conversion)

    ```
        E[Γ] ⊢ λx:T.u : ∀y:T, U
        E[Γ::(x:T)] ⊢ u =βδιζη (t x)
        -------------------
        E[Γ] ⊢ t =η λx:T.u
    ```

    It is legal to identify any term `t` of functional type `∀x:T, U` with its so-called η-expansion `λx:T.(t x)`.

    Here a special property is used: because of the generation rule for `E[Γ] ⊢ λx:T.u : ∀x:T, U`, x will not be contained in `Γ`.
    Note that this rule is 'convertible' but not 'reducible'.
    '''

    def __init__(self, wt : MP_WT, convert : MP_convertible):
        
        # proof of `E[Γ] ⊢ λx:T.u : ∀x:T, U`
        Meta_Sys_type_check(wt, MP_WT)
        if not isinstance(wt.t, Abstract) or not isinstance(wt.T, Prod):
            raise Meta_Sys_Error(f"Invalid term for η-expansion: '{wt}'.")

        # proof of `E[Γ::(x:T)] ⊢ u =βδιζη (t x)`
        Meta_Sys_type_check(convert, MP_convertible)
        if not isinstance(convert.t2, Apply):
            raise Meta_Sys_Error(f"Invalid conversion proof: '{convert}'.")

        # break `Γ::(x:T)`
        Gamma_pre, dec = convert.Gamma.pop()

        # consistent 'E'
        if not wt.E == convert.E:
            raise Meta_Sys_Error("Inconsistent environment.")
        
        # consitent 'Γ'
        if not wt.Gamma == Gamma_pre:
            raise Meta_Sys_Error("Inconsistent context.")
        
        # consistent 'x'
        if wt.t.x != dec.x or wt.t.x != convert.t2.u:
            raise Meta_Sys_Error("Inconsistent 'x'.")
        
        # consistent 'T'
        if wt.t.T != wt.T.T or wt.t.T != dec.T:
            raise Meta_Sys_Error("Inconsistent 'T'.")
        
        # consistent 'u'
        if wt.t.u != convert.t1:
            raise Meta_Sys_Error("Inconsistent 'u'.")
        
        self.__wt = wt
        self.__convert = convert

        # the proof `E[Γ] ⊢ t ~η λx:T.u`
        # complete

    @property
    def E(self) -> Environment:
        return self.__wt.E
    
    @property
    def Gamma(self) -> Context:
        return self.__wt.Gamma

    @property
    def t(self) -> Term:
        assert(isinstance(self.__convert.t2, Apply))
        return self.__convert.t2.t
    
    @property
    def lam(self) -> Abstract:
        assert(isinstance(self.__wt.t, Abstract))
        return self.__wt.t

    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__convert.conclusion() + "\n"
        return res
    
    def conclusion(self) -> str:
        return f"{self.E}{self.Gamma} ⊢ {self.t} =η {self.lam}"
    

@concrete_term
class MP_convertible(MetaProof):
    '''
    βδιζη-convertible.
    ```
        E[Γ] ⊢ t1 ▷ ... ▷ u1
        E[Γ] ⊢ t2 ▷ ... ▷ u2
        u1 ~α u2 or E[Γ] ⊢ u1 =η u2 or E[Γ] ⊢ u2 =η u1
        ----------------------------------
        E[Γ] ⊢ t1 =βδιζη t2
    ```
    Note : `E[Γ] ⊢ t1 ▷ ... ▷ u1` is also represented by `MP_reduction` because of transitivity object `MP_reduction_trans`.
    '''

    def __init__(self, red1 : MP_reduction, red2 : MP_reduction, u_eq_proof : None | MP_eta_conversion):
        '''
        u_eq_proof:
            - `None`: proof by alpha-conversion
            - `MP_eta_conversion` : proof by eta-conversion (automatically detect `u1` `u2`)
        '''

        # proof of `E[Γ] ⊢ t1 ▷ ... ▷ u1`
        Meta_Sys_type_check(red1, MP_reduction)

        # proof of `E[Γ] ⊢ t2 ▷ ... ▷ u2`
        Meta_Sys_type_check(red2, MP_reduction)

        # proof of `u1 ~α u2 or u1 ~η u2 or u2 ~η u1`
        Meta_Sys_type_check(u_eq_proof, (type(None), MP_eta_conversion))

        # consistent 'E'
        if red1.E != red2.E:
            raise Meta_Sys_Error("Inconsistent environment.")
        
        # consistent 'Γ'
        if red1.Gamma != red2.Gamma:
            raise Meta_Sys_Error("Inconsistent context.")

        # branch : proof by alpha-conversion
        if u_eq_proof is None:
            if not red1.t2.alpha_convertible(red2.t2):
                raise Meta_Sys_Error(f"βδιζη-convertible: proposed to proof by alpha-conversion, but '{red1.t2}' and '{red2.t2}' are not alpha-convertible.")
            
        # branch : proof by eta-conversion
        else:
            assert(isinstance(u_eq_proof, MP_eta_conversion))

            # consistent 'E'
            if u_eq_proof.E != red1.E:
                raise Meta_Sys_Error("Inconsistent environment.")
            
            # consistent 'Γ'
            if u_eq_proof.Gamma != red1.Gamma:
                raise Meta_Sys_Error("Inconsistent context.")

            if not ((red1.t2 == u_eq_proof.t and red2.t2 == u_eq_proof.lam) or (red1.t2 == u_eq_proof.lam and red2.t2 == u_eq_proof.t)):
                raise Meta_Sys_Error(f"Inconsistent eta-conversion proof : {u_eq_proof}.")

            
        self.__red1 = red1
        self.__red2 = red2
        self.__u_eq_proof = u_eq_proof


    @property
    def E(self) -> Environment:
        return self.__red1.E

    @property
    def Gamma(self) -> Context:
        return self.__red1.Gamma

    @property
    def t1(self) -> Term:
        return self.__red1.t1

    @property
    def t2(self) -> Term:
        return self.__red1.t2
    
    def premises(self) -> str:
        res = self.__red1.conclusion() + "\n"
        res += self.__red2.conclusion() + "\n"
        if self.__u_eq_proof is not None:
            res += self.__u_eq_proof.conclusion() + "\n"
        return res
    
    def conclusion(self) -> str:
        return f"{self.E}{self.Gamma} ⊢ {self.t1} =βδιζη {self.t2}"


##########################################################################
# Subtyping conversion.
###

@meta_term
class MP_subtyping(MetaProof):
    '''
    subtype
    ```
        E[Γ] ⊢ t1 ≤βδιζη t2
    ```
    '''

    def __init__(self, E : Environment, Gamma : Context, t1 : Term, t2 : Term):
        Meta_Sys_type_check(E, Environment)
        Meta_Sys_type_check(Gamma, Context)
        Meta_Sys_type_check(t1, Term)
        Meta_Sys_type_check(t2, Term)
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
        return f"{self.E}{self.Gamma} ⊢ {self.t1} ≤βδιζη {self.t2}"


