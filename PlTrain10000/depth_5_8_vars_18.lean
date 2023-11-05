variable (p7 p0 p6 p3 p5 p1 p2 p4 : Prop)
theorem file18_50 : (((((p0 ∧ False) → (p6 ∨ p0)) ∨ ((p2 ∧ p3) → (p7 → p5))) ∨ (((p1 ∧ p0) ∧ (p2 ∨ p1)) ∨ ((p5 → False) → (p1 ∨ p5)))) ∨ ((((p7 ∨ p4) → False) ∨ ((p1 ∧ p4) ∨ (p4 ∨ p3))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3


variable (p1 p7 p5 p0 p3 p2 : Prop)
theorem file18_435 : (((((p2 ∨ p3) → False) ∧ ((p2 → p2) → False)) → (((p3 → p0) ∨ (p7 → p3)) ∨ ((True → p1) → False))) ∨ ((((p1 ∧ p1) ∧ (p2 ∧ True)) ∨ ((p5 ∧ p5) → (p0 → False))) → False)) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inl
    apply Or.inl
    intro assump_12
    have assump_23 : (p2 → p2) := by
      intro assump_17
      exact assump_17
    let assump_16 := assump_7 assump_23
    apply False.elim assump_16


variable (p1 p6 p3 p0 p5 p4 : Prop)
theorem file18_959 : ((((((p5 → p1) ∧ (True → False)) → ((p6 → False) → (p3 → False))) ∨ (((p5 → p0) ∧ (p6 ∧ p1)) ∧ ((p3 ∨ True) ∨ (p3 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p5 → p1) ∧ (True → False)) → ((p6 → False) → (p3 → False))) ∨ (((p5 → p0) ∧ (p6 ∧ p1)) ∧ ((p3 ∨ True) ∨ (p3 ∨ p4)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      have assump_26 : True := by
        apply True.intro
      let assump_18 := assump_13 assump_26
      apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p0 p4 p5 p6 : Prop)
theorem file18_1657 : (((((True ∨ p6) → False) → ((p4 → False) → False)) ∧ (((p1 → False) ∧ (p6 ∧ p1)) ∧ ((p0 ∧ p0) → (p6 ∨ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_27 : p1 := by
            exact assump_13
          let assump_23 := assump_8 assump_27
          apply False.elim assump_23


variable (p1 p4 p5 p7 p2 p6 p0 : Prop)
theorem file18_2238 : (((((p6 → False) → (p4 ∨ p2)) ∧ ((p6 ∨ p7) → False)) ∧ (((p5 ∨ p7) → (p7 → p4)) ∨ ((p5 → p0) → (True ∧ p5)))) → ((((p7 ∧ p1) → (p4 ∧ False)) ∧ ((p2 → False) → (p5 ∨ p1))) → (((True ∨ p4) → False) → ((p7 ∨ p1) ∨ (p1 ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_13
        case inl assump_20 =>
          apply Or.inr
          apply Or.inr
          apply True.intro
        case inr assump_21 =>
          apply Or.inr
          apply Or.inr
          apply True.intro


variable (p6 p7 p1 p3 : Prop)
theorem file18_2976 : (((((True → False) → (False → p7)) → False) → False) ∨ ((((p6 ∧ p3) ∧ (p7 → p1)) ∧ ((p7 → True) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((True → False) → (False → p7)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p1 p5 p4 p6 p0 p7 p3 : Prop)
theorem file18_3383 : (((((False → False) ∨ (p7 ∨ p0)) → False) → (((p7 → False) ∨ (p6 → p0)) → ((p3 ∧ p6) ∨ (True → False)))) ∨ ((((p4 ∨ p1) ∨ (True → p3)) → False) ∧ (((False ∨ p5) → False) ∨ ((p5 → False) ∨ (p0 → p6))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inr
    intro assump_9
    have assump_33 : ((False → False) ∨ (p7 ∨ p0)) := by
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_1 assump_33
    apply False.elim assump_12
  case inr assump_4 =>
    apply Or.inr
    intro assump_23
    have assump_34 : ((False → False) ∨ (p7 ∨ p0)) := by
      apply Or.inl
      intro assump_27
      apply False.elim assump_27
    let assump_26 := assump_1 assump_34
    apply False.elim assump_26


variable (p6 p5 p0 p2 p4 p3 : Prop)
theorem file18_4240 : ((((((p3 → False) → False) → ((p5 ∨ p5) ∧ (p3 → True))) → (((p4 ∧ False) → False) ∨ ((p2 ∨ p6) → (p6 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 → False) → False) → ((p5 ∨ p5) ∧ (p3 → True))) → (((p4 ∧ False) → False) ∨ ((p2 ∨ p6) → (p6 ∨ p0)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p4 p5 p1 p0 p2 p3 : Prop)
theorem file18_4796 : (((((p5 ∧ False) ∧ (p5 → p5)) → ((p4 ∧ p2) → False)) → False) → ((((False → False) ∧ (p1 → p5)) → ((True ∨ p0) → (p3 → p6))) ∨ (((p3 ∧ p2) ∧ (p4 ∧ p0)) ∨ ((True ∨ False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    cases assump_4
    case intro assump_13 assump_14 =>
      have assump_74 : (((p5 ∧ False) ∧ (p5 → p5)) → ((p4 ∧ p2) → False)) := by
        intro assump_23
        intro assump_24
        cases assump_24
        case intro assump_25 assump_26 =>
          cases assump_23
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              apply False.elim assump_34
      let assump_22 := assump_1 assump_74
      apply False.elim assump_22
  case inr assump_10 =>
    cases assump_4
    case intro assump_44 assump_45 =>
      have assump_75 : (((p5 ∧ False) ∧ (p5 → p5)) → ((p4 ∧ p2) → False)) := by
        intro assump_55
        intro assump_56
        cases assump_56
        case intro assump_57 assump_58 =>
          cases assump_55
          case intro assump_63 assump_64 =>
            cases assump_63
            case intro assump_65 assump_66 =>
              apply False.elim assump_66
      let assump_54 := assump_1 assump_75
      apply False.elim assump_54


variable (p1 p7 p3 p2 p0 p4 p6 p5 : Prop)
theorem file18_6219 : (((((True → False) → False) ∨ ((p2 ∧ p1) → (p3 → p0))) ∨ (((False ∧ p2) ∧ (p1 ∧ p1)) ∧ ((p0 ∨ p5) ∨ (p4 → False)))) ∨ ((((p7 → True) → (p1 → p3)) → ((False ∧ p6) ∧ (p1 → p5))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p6 p4 p0 p7 : Prop)
theorem file18_6644 : ((((((p4 ∨ p2) ∧ (True ∧ p2)) → False) → False) ∧ ((((p7 ∧ p0) ∧ (False → p6)) ∨ ((p2 ∧ p0) ∧ (False → False))) ∧ (((p2 → p0) → False) ∨ ((p7 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_7
            case inl assump_20 =>
              have assump_66 : (p2 → p0) := by
                intro assump_25
                exact assump_13
              let assump_24 := assump_20 assump_66
              apply False.elim assump_24
            case inr assump_21 =>
              have assump_67 : (p7 → True) := by
                intro assump_34
                apply True.intro
              let assump_33 := assump_21 assump_67
              apply False.elim assump_33
      case inr assump_9 =>
        cases assump_9
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            cases assump_7
            case inl assump_48 =>
              have assump_68 : (p2 → p0) := by
                intro assump_53
                exact assump_41
              let assump_52 := assump_48 assump_68
              apply False.elim assump_52
            case inr assump_49 =>
              have assump_69 : (p7 → True) := by
                intro assump_62
                apply True.intro
              let assump_61 := assump_49 assump_69
              apply False.elim assump_61


variable (p3 p5 p7 p1 p0 p4 p6 p2 : Prop)
theorem file18_8363 : (((((p2 → True) ∨ (p7 ∧ p6)) ∨ ((False → p3) → False)) ∨ (((p5 → False) → False) → ((p7 ∧ p4) ∨ (p6 ∨ p1)))) ∨ ((((p0 → p4) ∨ (p7 ∧ True)) ∧ ((p5 → False) ∧ (p6 → False))) → (((p7 ∧ p1) → False) ∧ ((p2 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply True.intro


variable (p0 p1 p7 p3 p6 p5 p2 : Prop)
theorem file18_8751 : (((((True → False) → (False ∧ False)) → ((p5 ∧ p7) → (p3 → p5))) ∨ (((p0 → False) ∧ (p2 → False)) ∧ ((p1 → False) ∨ (p1 → p3)))) ∨ ((((p6 ∧ p0) ∨ (p1 → False)) → False) → (((p3 → False) ∧ (True → False)) → ((p3 ∧ p1) → (p1 ∨ p3))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    exact assump_6


variable (p1 p7 p0 p5 p4 p6 p3 : Prop)
theorem file18_9204 : (((((p0 ∧ p4) → (True ∧ p3)) → False) ∧ (((p5 → False) → False) ∧ ((False → False) → False))) → ((((p0 ∨ p6) ∧ (p6 ∨ p4)) ∨ ((p3 ∧ p5) → False)) ∧ (((p5 ∧ p5) → False) ∨ ((p1 → p7) → False)))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inr
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        have assump_54 : (False → False) := by
          intro assump_22
          apply False.elim assump_22
        let assump_21 := assump_7 assump_54
        apply False.elim assump_21
  cases assump_1
  case intro assump_28 assump_29 =>
    cases assump_29
    case intro assump_32 assump_33 =>
      apply Or.inl
      intro assump_38
      cases assump_38
      case intro assump_39 assump_40 =>
        have assump_55 : (False → False) := by
          intro assump_48
          apply False.elim assump_48
        let assump_47 := assump_33 assump_55
        apply False.elim assump_47


variable (p3 p0 p6 p7 p2 p1 : Prop)
theorem file18_10300 : (((((False ∨ False) ∧ (p6 → p2)) → ((p3 ∨ p1) → False)) ∧ (((False → False) → False) → False)) ∨ ((((p1 → False) ∨ (p7 ∨ False)) → ((p1 ∧ p0) → False)) ∧ (((p3 → False) → (p7 → p0)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_11
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    cases assump_11
    case intro assump_17 assump_18 =>
      cases assump_17
      case inl assump_19 =>
        apply False.elim assump_19
      case inr assump_20 =>
        apply False.elim assump_20
  case inr assump_14 =>
    cases assump_11
    case intro assump_27 assump_28 =>
      cases assump_27
      case inl assump_29 =>
        apply False.elim assump_29
      case inr assump_30 =>
        apply False.elim assump_30
  intro assump_35
  have assump_45 : (False → False) := by
    intro assump_39
    apply False.elim assump_39
  let assump_38 := assump_35 assump_45
  apply False.elim assump_38


variable (p7 p5 p0 p2 p6 p4 p1 p3 : Prop)
theorem file18_11290 : (((((p6 ∧ p0) ∨ (False → p2)) ∨ ((p5 → False) ∧ (p6 ∨ False))) ∨ (((False ∨ p2) ∧ (p2 ∧ p1)) ∨ ((p7 → False) ∨ (p2 ∧ p4)))) ∨ ((((True → False) → (p6 ∧ p3)) ∧ ((p1 → False) ∨ (p2 → p6))) ∨ (((p0 ∧ p6) → (True → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_5
  apply False.elim assump_5


variable (p0 p4 p1 p3 p7 p5 : Prop)
theorem file18_11691 : ((((((p7 ∨ p0) ∨ (p7 ∧ p7)) → ((True → p0) ∧ (p4 → False))) → (((p1 → p0) → (False ∨ True)) ∨ ((False → False) ∨ (p3 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p7 ∨ p0) ∨ (p7 ∧ p7)) → ((True → p0) ∧ (p4 → False))) → (((p1 → p0) → (False ∨ True)) ∨ ((False → False) ∨ (p3 ∨ p5)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p0 : Prop)
theorem file18_12213 : (((((False → False) → (False → False)) → ((p6 → True) ∨ (True ∧ p0))) → False) → False) := by
  intro assump_14
  have assump_25 : (((False → False) → (False → False)) → ((p6 → True) ∨ (True ∧ p0))) := by
    intro assump_18
    apply Or.inl
    intro assump_21
    apply True.intro
  let assump_17 := assump_14 assump_25
  apply False.elim assump_17


variable (p3 p5 p6 p0 : Prop)
theorem file18_12618 : (((((p0 → False) ∨ (p6 → False)) → False) ∧ (((p0 ∧ p5) ∧ (p3 ∨ p5)) ∧ ((p3 → p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case inl assump_16 =>
            have assump_40 : (p3 → p5) := by
              intro assump_23
              exact assump_11
            let assump_22 := assump_7 assump_40
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_41 : (p3 → p5) := by
              intro assump_34
              exact assump_17
            let assump_33 := assump_7 assump_41
            apply False.elim assump_33


variable (p4 p7 p0 p3 : Prop)
theorem file18_13500 : ((((((True → False) → False) → False) → (((p0 ∧ p4) ∧ (p0 → p3)) ∧ ((p7 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_67 : ((((True → False) → False) → False) → (((p0 ∧ p4) ∧ (p0 → p3)) ∧ ((p7 → False) → False))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    have assump_68 : ((True → False) → False) := by
      intro assump_9
      have assump_69 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_69
      apply False.elim assump_12
    let assump_8 := assump_5 assump_68
    apply False.elim assump_8
    have assump_70 : ((True → False) → False) := by
      intro assump_22
      have assump_71 : True := by
        apply True.intro
      let assump_25 := assump_22 assump_71
      apply False.elim assump_25
    let assump_21 := assump_5 assump_70
    apply False.elim assump_21
    intro assump_32
    have assump_72 : ((True → False) → False) := by
      intro assump_38
      have assump_73 : True := by
        apply True.intro
      let assump_41 := assump_38 assump_73
      apply False.elim assump_41
    let assump_37 := assump_5 assump_72
    apply False.elim assump_37
    intro assump_48
    have assump_74 : ((True → False) → False) := by
      intro assump_54
      have assump_75 : True := by
        apply True.intro
      let assump_57 := assump_54 assump_75
      apply False.elim assump_57
    let assump_53 := assump_5 assump_74
    apply False.elim assump_53
  let assump_4 := assump_1 assump_67
  apply False.elim assump_4


variable (p6 p2 p3 p1 p7 p4 : Prop)
theorem file18_15108 : (((((True → p6) → False) → False) → (((p1 → p2) → (p3 → True)) ∨ ((p7 ∧ False) → False))) ∨ ((((p3 → False) → False) → ((p3 → False) ∧ (p2 ∧ p4))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p0 p6 p2 p5 p4 p7 p3 : Prop)
theorem file18_15434 : (((((p7 ∧ False) → False) → False) → (((p7 → p2) ∧ (False → False)) ∧ ((p6 ∧ False) → (p3 → p2)))) ∨ ((((p5 → True) ∧ (p6 ∨ p4)) → False) ∧ (((False → False) → False) ∨ ((p6 ∨ p6) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_31 : ((p7 ∧ False) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_7 := assump_1 assump_31
  apply False.elim assump_7
  intro assump_18
  apply False.elim assump_18
  intro assump_21
  intro assump_22
  cases assump_21
  case intro assump_25 assump_26 =>
    apply False.elim assump_26


variable (p5 p4 p0 p1 p6 p2 p7 p3 : Prop)
theorem file18_16179 : ((((((p0 ∧ p2) ∧ (p1 ∧ True)) ∧ ((p5 → False) ∧ (p6 → True))) → (((p3 ∨ p5) ∧ (p0 ∨ True)) → ((p2 ∧ p7) → False))) ∧ ((((True ∧ p2) → False) → ((p5 → p7) ∨ (p1 → False))) ∧ (((p4 → p4) → (p6 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((p4 → p4) → (p6 ∨ True)) := by
        intro assump_13
        apply Or.inr
        apply True.intro
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p3 p0 p6 p5 : Prop)
theorem file18_16782 : (((((True ∨ p3) ∧ (p5 ∧ p5)) ∨ ((p0 → p6) → (p3 → True))) → False) → False) := by
  intro assump_1
  have assump_10 : (((True ∨ p3) ∧ (p5 ∧ p5)) ∨ ((p0 → p6) → (p3 → True))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p5 p2 p7 : Prop)
theorem file18_17154 : ((((((p7 ∧ p2) → (False ∧ p5)) ∧ ((True → True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p7 ∧ p2) → (False ∧ p5)) ∧ ((True → True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : (True → True) := by
        intro assump_13
        apply True.intro
      let assump_12 := assump_7 assump_21
      apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p4 p7 p5 p1 p3 : Prop)
theorem file18_17715 : ((((((True → False) → False) → False) → (((p4 ∨ p1) ∨ (p4 → p4)) → ((p3 ∧ p7) → (p5 ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((True → False) → False) → False) → (((p4 ∨ p1) ∨ (p4 → p4)) → ((p3 ∧ p7) → (p5 ∨ p7)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case inl assump_14 =>
        cases assump_14
        case inl assump_16 =>
          apply Or.inr
          exact assump_9
        case inr assump_17 =>
          apply Or.inr
          exact assump_9
      case inr assump_15 =>
        apply Or.inr
        exact assump_9
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p7 p4 p5 p2 p1 : Prop)
theorem file18_18500 : (((((p2 ∧ p2) ∧ (p1 → False)) → ((p2 → False) ∨ (p5 → False))) ∧ (((True ∨ p1) ∨ (p4 ∧ False)) → False)) → ((((p5 ∨ p4) ∧ (p7 → False)) ∨ ((p4 → False) ∧ (p2 ∨ p7))) → False)) := by
  intro assump_16
  intro assump_17
  cases assump_17
  case inl assump_18 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_16
        case intro assump_28 assump_29 =>
          have assump_82 : ((True ∨ p1) ∨ (p4 ∧ False)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_34 := assump_29 assump_82
          apply False.elim assump_34
      case inr assump_23 =>
        cases assump_16
        case intro assump_42 assump_43 =>
          have assump_83 : ((True ∨ p1) ∨ (p4 ∧ False)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_48 := assump_43 assump_83
          apply False.elim assump_48
  case inr assump_19 =>
    cases assump_19
    case intro assump_52 assump_53 =>
      cases assump_53
      case inl assump_56 =>
        cases assump_16
        case intro assump_60 assump_61 =>
          have assump_84 : ((True ∨ p1) ∨ (p4 ∧ False)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_66 := assump_61 assump_84
          apply False.elim assump_66
      case inr assump_57 =>
        cases assump_16
        case intro assump_72 assump_73 =>
          have assump_85 : ((True ∨ p1) ∨ (p4 ∧ False)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_78 := assump_73 assump_85
          apply False.elim assump_78


variable (p4 p5 p7 p2 p1 p3 p6 : Prop)
theorem file18_20283 : ((((((p1 ∧ True) ∧ (p2 ∨ False)) → ((p5 ∧ p5) ∧ (p3 ∧ p2))) ∧ (((p2 → p1) ∨ (p2 → True)) ∧ ((True ∧ False) ∧ (p2 → False)))) ∧ ((((p5 ∧ True) ∨ (p2 → p1)) ∧ ((p3 → p1) ∧ (p6 ∧ p5))) ∨ (((False ∧ p5) ∨ (p4 → False)) ∨ ((p4 ∨ p6) → (p7 ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
        case inr assump_11 =>
          cases assump_9
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              apply False.elim assump_27


variable (p2 p0 p1 p6 p4 p5 p3 p7 : Prop)
theorem file18_21241 : (((((p4 → False) → (p5 ∨ p6)) ∨ ((p1 → p5) → False)) ∧ (((p4 → p1) ∨ (True ∧ p7)) ∧ ((p3 ∧ p5) → False))) → ((((p3 → False) → (p4 ∧ p3)) ∨ ((p3 ∧ True) → False)) → (((p1 ∧ p4) ∨ (p0 ∨ p2)) → ((p7 ∨ True) → (True ∨ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_3
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_2
        case inl assump_17 =>
          cases assump_1
          case intro assump_21 assump_22 =>
            cases assump_21
            case inl assump_23 =>
              cases assump_22
              case intro assump_27 assump_28 =>
                cases assump_27
                case inl assump_29 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_30 =>
                  cases assump_30
                  case intro assump_35 assump_36 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_24 =>
              cases assump_22
              case intro assump_45 assump_46 =>
                cases assump_45
                case inl assump_47 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_48 =>
                  cases assump_48
                  case intro assump_53 assump_54 =>
                    apply Or.inl
                    apply True.intro
        case inr assump_18 =>
          cases assump_1
          case intro assump_63 assump_64 =>
            cases assump_63
            case inl assump_65 =>
              cases assump_64
              case intro assump_69 assump_70 =>
                cases assump_69
                case inl assump_71 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_72 =>
                  cases assump_72
                  case intro assump_77 assump_78 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_66 =>
              cases assump_64
              case intro assump_87 assump_88 =>
                cases assump_87
                case inl assump_89 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_90 =>
                  cases assump_90
                  case intro assump_95 assump_96 =>
                    apply Or.inl
                    apply True.intro
    case inr assump_10 =>
      cases assump_10
      case inl assump_103 =>
        cases assump_2
        case inl assump_107 =>
          cases assump_1
          case intro assump_111 assump_112 =>
            cases assump_111
            case inl assump_113 =>
              cases assump_112
              case intro assump_117 assump_118 =>
                cases assump_117
                case inl assump_119 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_120 =>
                  cases assump_120
                  case intro assump_125 assump_126 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_114 =>
              cases assump_112
              case intro assump_135 assump_136 =>
                cases assump_135
                case inl assump_137 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_138 =>
                  cases assump_138
                  case intro assump_143 assump_144 =>
                    apply Or.inl
                    apply True.intro
        case inr assump_108 =>
          cases assump_1
          case intro assump_153 assump_154 =>
            cases assump_153
            case inl assump_155 =>
              cases assump_154
              case intro assump_159 assump_160 =>
                cases assump_159
                case inl assump_161 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_162 =>
                  cases assump_162
                  case intro assump_167 assump_168 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_156 =>
              cases assump_154
              case intro assump_177 assump_178 =>
                cases assump_177
                case inl assump_179 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_180 =>
                  cases assump_180
                  case intro assump_185 assump_186 =>
                    apply Or.inl
                    apply True.intro
      case inr assump_104 =>
        cases assump_2
        case inl assump_195 =>
          cases assump_1
          case intro assump_199 assump_200 =>
            cases assump_199
            case inl assump_201 =>
              cases assump_200
              case intro assump_205 assump_206 =>
                cases assump_205
                case inl assump_207 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_208 =>
                  cases assump_208
                  case intro assump_213 assump_214 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_202 =>
              cases assump_200
              case intro assump_223 assump_224 =>
                cases assump_223
                case inl assump_225 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_226 =>
                  cases assump_226
                  case intro assump_231 assump_232 =>
                    apply Or.inl
                    apply True.intro
        case inr assump_196 =>
          cases assump_1
          case intro assump_241 assump_242 =>
            cases assump_241
            case inl assump_243 =>
              cases assump_242
              case intro assump_247 assump_248 =>
                cases assump_247
                case inl assump_249 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_250 =>
                  cases assump_250
                  case intro assump_255 assump_256 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_244 =>
              cases assump_242
              case intro assump_265 assump_266 =>
                cases assump_265
                case inl assump_267 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_268 =>
                  cases assump_268
                  case intro assump_273 assump_274 =>
                    apply Or.inl
                    apply True.intro
  case inr assump_6 =>
    cases assump_3
    case inl assump_283 =>
      cases assump_283
      case intro assump_285 assump_286 =>
        cases assump_2
        case inl assump_291 =>
          cases assump_1
          case intro assump_295 assump_296 =>
            cases assump_295
            case inl assump_297 =>
              cases assump_296
              case intro assump_301 assump_302 =>
                cases assump_301
                case inl assump_303 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_304 =>
                  cases assump_304
                  case intro assump_309 assump_310 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_298 =>
              cases assump_296
              case intro assump_319 assump_320 =>
                cases assump_319
                case inl assump_321 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_322 =>
                  cases assump_322
                  case intro assump_327 assump_328 =>
                    apply Or.inl
                    apply True.intro
        case inr assump_292 =>
          cases assump_1
          case intro assump_337 assump_338 =>
            cases assump_337
            case inl assump_339 =>
              cases assump_338
              case intro assump_343 assump_344 =>
                cases assump_343
                case inl assump_345 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_346 =>
                  cases assump_346
                  case intro assump_351 assump_352 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_340 =>
              cases assump_338
              case intro assump_361 assump_362 =>
                cases assump_361
                case inl assump_363 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_364 =>
                  cases assump_364
                  case intro assump_369 assump_370 =>
                    apply Or.inl
                    apply True.intro
    case inr assump_284 =>
      cases assump_284
      case inl assump_377 =>
        cases assump_2
        case inl assump_381 =>
          cases assump_1
          case intro assump_385 assump_386 =>
            cases assump_385
            case inl assump_387 =>
              cases assump_386
              case intro assump_391 assump_392 =>
                cases assump_391
                case inl assump_393 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_394 =>
                  cases assump_394
                  case intro assump_399 assump_400 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_388 =>
              cases assump_386
              case intro assump_409 assump_410 =>
                cases assump_409
                case inl assump_411 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_412 =>
                  cases assump_412
                  case intro assump_417 assump_418 =>
                    apply Or.inl
                    apply True.intro
        case inr assump_382 =>
          cases assump_1
          case intro assump_427 assump_428 =>
            cases assump_427
            case inl assump_429 =>
              cases assump_428
              case intro assump_433 assump_434 =>
                cases assump_433
                case inl assump_435 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_436 =>
                  cases assump_436
                  case intro assump_441 assump_442 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_430 =>
              cases assump_428
              case intro assump_451 assump_452 =>
                cases assump_451
                case inl assump_453 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_454 =>
                  cases assump_454
                  case intro assump_459 assump_460 =>
                    apply Or.inl
                    apply True.intro
      case inr assump_378 =>
        cases assump_2
        case inl assump_469 =>
          cases assump_1
          case intro assump_473 assump_474 =>
            cases assump_473
            case inl assump_475 =>
              cases assump_474
              case intro assump_479 assump_480 =>
                cases assump_479
                case inl assump_481 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_482 =>
                  cases assump_482
                  case intro assump_487 assump_488 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_476 =>
              cases assump_474
              case intro assump_497 assump_498 =>
                cases assump_497
                case inl assump_499 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_500 =>
                  cases assump_500
                  case intro assump_505 assump_506 =>
                    apply Or.inl
                    apply True.intro
        case inr assump_470 =>
          cases assump_1
          case intro assump_515 assump_516 =>
            cases assump_515
            case inl assump_517 =>
              cases assump_516
              case intro assump_521 assump_522 =>
                cases assump_521
                case inl assump_523 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_524 =>
                  cases assump_524
                  case intro assump_529 assump_530 =>
                    apply Or.inl
                    apply True.intro
            case inr assump_518 =>
              cases assump_516
              case intro assump_539 assump_540 =>
                cases assump_539
                case inl assump_541 =>
                  apply Or.inl
                  apply True.intro
                case inr assump_542 =>
                  cases assump_542
                  case intro assump_547 assump_548 =>
                    apply Or.inl
                    apply True.intro


variable (p6 p1 p5 : Prop)
theorem file18_34591 : ((((((True → False) ∧ (p1 → False)) → False) ∨ (((p5 ∨ p6) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_20 : ((((True → False) ∧ (p1 → False)) → False) ∨ (((p5 ∨ p6) → False) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 p7 p0 p5 p2 p6 : Prop)
theorem file18_35161 : ((((((p6 ∧ p0) ∧ (p5 → p5)) → False) → (((p1 ∨ p2) ∨ (False ∨ p2)) ∨ ((p0 → False) ∧ (p1 ∧ p7)))) ∧ ((((p6 → p2) ∨ (True ∧ p6)) → ((p6 ∨ p5) → (True ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_40 : (((p6 → p2) ∨ (True ∧ p6)) → ((p6 ∨ p5) → (True ∨ p1))) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        cases assump_9
        case inl assump_15 =>
          apply Or.inl
          apply True.intro
        case inr assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            apply Or.inl
            apply True.intro
      case inr assump_12 =>
        cases assump_9
        case inl assump_27 =>
          apply Or.inl
          apply True.intro
        case inr assump_28 =>
          cases assump_28
          case intro assump_31 assump_32 =>
            apply Or.inl
            apply True.intro
    let assump_8 := assump_3 assump_40
    apply False.elim assump_8


variable (p4 p7 p2 p1 p3 p6 p5 p0 : Prop)
theorem file18_36264 : (((((p4 ∨ p4) ∧ (p6 ∨ p4)) → ((p2 ∧ p5) ∨ (p7 → p7))) ∨ (((p2 → True) ∧ (p7 ∧ p0)) ∧ ((p1 ∧ p1) ∧ (p5 ∨ False)))) ∨ ((((False → True) → (p5 ∨ p4)) ∨ ((p5 ∧ p3) ∧ (p3 → False))) → (((p6 ∨ p5) ∨ (p3 → False)) ∨ ((p4 ∧ p2) → (p2 ∨ p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        apply Or.inr
        intro assump_12
        exact assump_12
      case inr assump_9 =>
        apply Or.inr
        intro assump_17
        exact assump_17
    case inr assump_5 =>
      cases assump_3
      case inl assump_22 =>
        apply Or.inr
        intro assump_26
        exact assump_26
      case inr assump_23 =>
        apply Or.inr
        intro assump_31
        exact assump_31


variable (p2 p6 p3 p1 p5 : Prop)
theorem file18_37158 : (((((p2 ∨ True) → False) → False) → False) → ((((p3 ∧ True) → (p6 ∧ p1)) → ((p2 → False) ∧ (p5 ∨ p3))) ∧ (((p6 → p1) → False) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  intro assump_3
  have assump_52 : (((p2 ∨ True) → False) → False) := by
    intro assump_11
    have assump_53 : (p2 ∨ True) := by
      apply Or.inl
      exact assump_3
    let assump_14 := assump_11 assump_53
    apply False.elim assump_14
  let assump_10 := assump_1 assump_52
  apply False.elim assump_10
  have assump_54 : (((p2 ∨ True) → False) → False) := by
    intro assump_26
    have assump_55 : (p2 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_29 := assump_26 assump_55
    apply False.elim assump_29
  let assump_25 := assump_1 assump_54
  apply False.elim assump_25
  intro assump_36
  have assump_56 : (((p2 ∨ True) → False) → False) := by
    intro assump_42
    have assump_57 : (p2 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_45 := assump_42 assump_57
    apply False.elim assump_45
  let assump_41 := assump_1 assump_56
  apply False.elim assump_41


variable (p4 p3 p6 p2 p7 : Prop)
theorem file18_38352 : ((((((p4 ∨ p6) → False) → ((p7 ∨ p7) ∨ (p6 → False))) ∨ (((p2 ∧ p3) ∧ (p3 → False)) → ((p6 ∨ False) → (p3 → p4)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p4 ∨ p6) → False) → ((p7 ∨ p7) ∨ (p6 → False))) ∨ (((p2 ∧ p3) ∧ (p3 → False)) → ((p6 ∨ False) → (p3 → p4)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_20 : (p4 ∨ p6) := by
      apply Or.inr
      exact assump_8
    let assump_12 := assump_5 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p3 p6 p4 p5 p1 p0 p7 : Prop)
theorem file18_38994 : (((((p6 → p3) → (p1 ∨ p0)) ∧ ((p1 → False) → (p3 ∨ p1))) → (((p3 ∨ p7) ∧ (True → False)) → ((False ∨ False) ∧ (p6 → False)))) → ((((p1 → p5) → (p7 ∨ True)) ∨ ((p6 ∧ p7) → False)) ∧ (((p5 → p3) ∨ (p4 ∨ p7)) → ((p7 → False) → (True ∧ True))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  apply Or.inr
  apply True.intro
  intro assump_7
  intro assump_8
  apply And.intro
  apply True.intro
  apply True.intro


variable (p1 p2 p0 p7 p3 p4 : Prop)
theorem file18_39493 : (((((p1 ∧ False) ∧ (p3 → False)) ∧ ((p0 ∧ p1) → (p2 ∧ p3))) → (((p0 ∨ True) ∧ (False → False)) → ((p1 → False) → (p7 ∨ p7)))) ∨ ((((p3 ∧ p4) → (p3 → p2)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply False.elim assump_19
    case inr assump_9 =>
      cases assump_1
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            apply False.elim assump_33


variable (p7 p3 p0 p1 p2 p4 p6 p5 : Prop)
theorem file18_40396 : ((((((False ∧ p2) ∧ (p5 ∧ p7)) ∧ ((p0 ∨ False) → (p6 ∨ False))) ∧ (((False → p7) ∨ (p2 → p0)) ∨ ((False → False) → False))) ∧ ((((p6 ∨ p6) ∨ (p0 ∧ True)) → ((p5 ∨ True) → (False → p4))) ∨ (((False → p3) ∨ (p6 → False)) ∧ ((p1 → False) ∧ (p3 ∧ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            apply False.elim assump_10


variable (p3 p4 p1 p2 : Prop)
theorem file18_41069 : (((((p1 ∧ False) → (p4 → False)) → False) ∧ (((False ∧ p2) ∧ (p3 ∨ True)) ∨ ((p4 ∧ p3) → False))) → ((((p2 ∧ p4) ∧ (p2 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
    case inr assump_10 =>
      have assump_34 : ((p1 ∧ False) → (p4 → False)) := by
        intro assump_21
        intro assump_22
        cases assump_21
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
      let assump_20 := assump_5 assump_34
      apply False.elim assump_20


variable (p4 p7 p2 p3 p5 p0 : Prop)
theorem file18_41887 : (((((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) → False) → ((((True → False) ∨ (p3 → False)) ∨ ((p3 ∨ True) ∧ (p3 ∨ p4))) → (((p7 ∧ p0) ∨ (p0 → False)) → ((p0 → p2) → False)))) := by
  intro assump_31
  intro assump_32
  intro assump_33
  intro assump_34
  cases assump_33
  case inl assump_37 =>
    cases assump_37
    case intro assump_39 assump_40 =>
      cases assump_32
      case inl assump_45 =>
        cases assump_45
        case inl assump_47 =>
          have assump_325 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
            intro assump_54
            intro assump_55
            have assump_326 : True := by
              apply True.intro
            let assump_64 := assump_55 assump_326
            apply False.elim assump_64
          let assump_53 := assump_31 assump_325
          apply False.elim assump_53
        case inr assump_48 =>
          have assump_327 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
            intro assump_76
            intro assump_77
            have assump_328 : True := by
              apply True.intro
            let assump_86 := assump_77 assump_328
            apply False.elim assump_86
          let assump_75 := assump_31 assump_327
          apply False.elim assump_75
      case inr assump_46 =>
        cases assump_46
        case intro assump_93 assump_94 =>
          cases assump_93
          case inl assump_95 =>
            cases assump_94
            case inl assump_99 =>
              have assump_329 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
                intro assump_106
                intro assump_107
                have assump_330 : True := by
                  apply True.intro
                let assump_116 := assump_107 assump_330
                apply False.elim assump_116
              let assump_105 := assump_31 assump_329
              apply False.elim assump_105
            case inr assump_100 =>
              have assump_331 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
                intro assump_128
                intro assump_129
                have assump_332 : True := by
                  apply True.intro
                let assump_138 := assump_129 assump_332
                apply False.elim assump_138
              let assump_127 := assump_31 assump_331
              apply False.elim assump_127
          case inr assump_96 =>
            cases assump_94
            case inl assump_147 =>
              have assump_333 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
                intro assump_154
                intro assump_155
                have assump_334 : True := by
                  apply True.intro
                let assump_164 := assump_155 assump_334
                apply False.elim assump_164
              let assump_153 := assump_31 assump_333
              apply False.elim assump_153
            case inr assump_148 =>
              have assump_335 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
                intro assump_176
                intro assump_177
                have assump_336 : True := by
                  apply True.intro
                let assump_186 := assump_177 assump_336
                apply False.elim assump_186
              let assump_175 := assump_31 assump_335
              apply False.elim assump_175
  case inr assump_38 =>
    cases assump_32
    case inl assump_195 =>
      cases assump_195
      case inl assump_197 =>
        have assump_337 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
          intro assump_204
          intro assump_205
          have assump_338 : True := by
            apply True.intro
          let assump_211 := assump_205 assump_338
          apply False.elim assump_211
        let assump_203 := assump_31 assump_337
        apply False.elim assump_203
      case inr assump_198 =>
        have assump_339 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
          intro assump_223
          intro assump_224
          have assump_340 : True := by
            apply True.intro
          let assump_230 := assump_224 assump_340
          apply False.elim assump_230
        let assump_222 := assump_31 assump_339
        apply False.elim assump_222
    case inr assump_196 =>
      cases assump_196
      case intro assump_237 assump_238 =>
        cases assump_237
        case inl assump_239 =>
          cases assump_238
          case inl assump_243 =>
            have assump_341 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
              intro assump_250
              intro assump_251
              have assump_342 : True := by
                apply True.intro
              let assump_257 := assump_251 assump_342
              apply False.elim assump_257
            let assump_249 := assump_31 assump_341
            apply False.elim assump_249
          case inr assump_244 =>
            have assump_343 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
              intro assump_269
              intro assump_270
              have assump_344 : True := by
                apply True.intro
              let assump_276 := assump_270 assump_344
              apply False.elim assump_276
            let assump_268 := assump_31 assump_343
            apply False.elim assump_268
        case inr assump_240 =>
          cases assump_238
          case inl assump_285 =>
            have assump_345 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
              intro assump_292
              intro assump_293
              have assump_346 : True := by
                apply True.intro
              let assump_299 := assump_293 assump_346
              apply False.elim assump_299
            let assump_291 := assump_31 assump_345
            apply False.elim assump_291
          case inr assump_286 =>
            have assump_347 : (((p0 ∧ True) → (p5 ∧ p4)) → ((True → False) → False)) := by
              intro assump_311
              intro assump_312
              have assump_348 : True := by
                apply True.intro
              let assump_318 := assump_312 assump_348
              apply False.elim assump_318
            let assump_310 := assump_31 assump_347
            apply False.elim assump_310


variable (p1 p0 p4 p3 p7 : Prop)
theorem file18_48280 : ((((((p3 → True) ∨ (p4 ∨ False)) ∧ ((p1 → True) → False)) → False) ∧ ((((p1 ∨ p1) → (p7 → False)) ∧ ((p0 ∨ p0) → (False → False))) ∧ (((p3 ∧ p0) → False) ∧ ((p4 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          have assump_25 : (p4 → True) := by
            intro assump_21
            apply True.intro
          let assump_20 := assump_15 assump_25
          apply False.elim assump_20


variable (p1 p4 p6 p0 p2 p7 : Prop)
theorem file18_48969 : (((((p7 → True) ∧ (p0 ∨ False)) → ((p2 ∧ p0) ∨ (True ∨ p0))) ∨ (((True ∨ True) ∧ (True → p4)) → False)) ∨ ((((p7 ∧ False) ∧ (True → p6)) → ((True ∨ p1) ∨ (p2 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inr
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply False.elim assump_7


variable (p2 p6 p0 p7 p3 p1 p5 p4 : Prop)
theorem file18_49480 : (((((p0 → p2) → (p4 → p6)) → False) → (((p6 ∨ p1) → (p2 ∨ True)) ∨ ((p5 ∨ False) → (p5 ∧ p2)))) ∨ ((((p6 → False) ∧ (p0 ∨ p0)) ∨ ((True ∧ p3) ∨ (p1 → False))) ∨ (((p4 ∨ False) → (False ∧ p7)) → ((p5 → p0) → (p3 → False))))) := by
  apply Or.inl
  intro assump_11
  apply Or.inl
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    apply Or.inr
    apply True.intro
  case inr assump_16 =>
    apply Or.inr
    apply True.intro


variable (p7 p1 p5 p4 p2 p6 : Prop)
theorem file18_49978 : ((((((p6 → p4) ∧ (p4 → False)) → ((p4 → False) → (p1 → p7))) ∧ (((p6 → False) ∧ (True → False)) ∨ ((p2 → p1) → False))) ∧ ((((p2 ∧ p1) ∧ (p5 → False)) ∨ ((False → False) ∨ (p1 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_36 : (((p2 ∧ p1) ∧ (p5 → False)) ∨ ((False → False) ∨ (p1 → False))) := by
            apply Or.inr
            apply Or.inl
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_3 assump_36
          apply False.elim assump_18
      case inr assump_9 =>
        have assump_37 : (((p2 ∧ p1) ∧ (p5 → False)) ∨ ((False → False) ∨ (p1 → False))) := by
          apply Or.inr
          apply Or.inl
          intro assump_30
          apply False.elim assump_30
        let assump_29 := assump_3 assump_37
        apply False.elim assump_29


variable (p3 p5 : Prop)
theorem file18_51081 : ((((((p5 → False) → False) → False) → False) ∧ ((((p5 → p5) ∨ (True → False)) → ((p3 → p3) ∨ (p3 ∧ p3))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_29 : (((p5 → p5) ∨ (True → False)) → ((p3 → p3) ∨ (p3 ∧ p3))) := by
      intro assump_13
      cases assump_13
      case inl assump_14 =>
        apply Or.inl
        intro assump_18
        exact assump_18
      case inr assump_15 =>
        apply Or.inl
        intro assump_23
        exact assump_23
    let assump_12 := assump_7 assump_29
    apply False.elim assump_12


variable (p7 p3 p5 p2 p0 p4 p1 : Prop)
theorem file18_51735 : (((((p2 ∨ p3) ∨ (p3 → True)) ∧ ((p7 ∨ p1) ∨ (p4 ∨ p0))) → False) → ((((p4 → p0) ∨ (True → p0)) → ((True → False) ∧ (p5 → False))) → (((p0 ∨ False) → False) ∧ ((p7 ∨ p5) ∧ (p4 → False))))) := by
  intro assump_5
  intro assump_6
  apply And.intro
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    have assump_56 : (((p2 ∨ p3) ∨ (p3 → True)) ∧ ((p7 ∨ p1) ∨ (p4 ∨ p0))) := by
      apply And.intro
      apply Or.inr
      intro assump_17
      apply True.intro
      apply Or.inr
      apply Or.inr
      exact assump_8
    let assump_16 := assump_5 assump_56
    apply False.elim assump_16
  case inr assump_9 =>
    apply False.elim assump_9
  apply And.intro
  have assump_57 : ((p4 → p0) ∨ (True → p0)) := by
    apply Or.inl
    intro assump_30
    have assump_58 : (((p2 ∨ p3) ∨ (p3 → True)) ∧ ((p7 ∨ p1) ∨ (p4 ∨ p0))) := by
      apply And.intro
      apply Or.inr
      intro assump_35
      apply True.intro
      apply Or.inr
      apply Or.inl
      exact assump_30
    let assump_34 := assump_5 assump_58
    apply False.elim assump_34
  let assump_29 := assump_6 assump_57
  let assump_39 := And.left assump_29
  have assump_59 : True := by
    apply True.intro
  let assump_40 := assump_39 assump_59
  apply False.elim assump_40
  intro assump_44
  have assump_60 : (((p2 ∨ p3) ∨ (p3 → True)) ∧ ((p7 ∨ p1) ∨ (p4 ∨ p0))) := by
    apply And.intro
    apply Or.inr
    intro assump_52
    apply True.intro
    apply Or.inr
    apply Or.inl
    exact assump_44
  let assump_51 := assump_5 assump_60
  apply False.elim assump_51


variable (p1 p3 p0 p4 p6 p5 : Prop)
theorem file18_53343 : (((((p6 → p4) ∧ (p0 ∧ p1)) ∧ ((p6 → False) → (p3 → False))) ∧ (((p1 ∧ p0) ∨ (p0 → p3)) ∧ ((p5 ∨ True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                have assump_42 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_30 := assump_19 assump_42
                apply False.elim assump_30
            case inr assump_21 =>
              have assump_43 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_38 := assump_19 assump_43
              apply False.elim assump_38


variable (p1 p4 p3 p6 p7 p5 p0 : Prop)
theorem file18_54440 : (((((p3 ∧ p7) → (p7 → p6)) ∧ ((p0 → p0) → False)) → (((p3 ∨ p1) → (True → p7)) → False)) ∨ ((((p1 ∧ False) ∧ (p5 ∨ p7)) ∨ ((p4 ∨ p6) ∨ (False ∧ p5))) → (((p3 → False) ∧ (p7 ∧ p0)) ∧ ((p6 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_18 : (p0 → p0) := by
      intro assump_12
      exact assump_12
    let assump_11 := assump_6 assump_18
    apply False.elim assump_11


variable (p2 p4 : Prop)
theorem file18_54954 : (((((False → False) ∨ (p4 → False)) ∧ ((p4 ∨ False) ∨ (True ∨ p2))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → False) ∨ (p4 → False)) ∧ ((p4 ∨ False) ∨ (True ∨ p2))) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p6 p2 p1 p3 p0 : Prop)
theorem file18_55420 : ((((((p0 → True) ∨ (p1 → p5)) ∧ ((p6 → p2) → False)) → (((p1 → p2) → False) → ((False ∨ p3) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p0 → True) ∨ (p1 → p5)) ∧ ((p6 → p2) → False)) → (((p1 → p2) → False) → ((False ∨ p3) ∨ (False → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inr
        intro assump_17
        apply False.elim assump_17
      case inr assump_12 =>
        apply Or.inr
        intro assump_24
        apply False.elim assump_24
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p0 p5 p6 p1 p7 : Prop)
theorem file18_56166 : (((((p0 → False) → (True ∨ True)) → ((False → False) ∨ (p7 → False))) → False) → ((((p1 → False) → (p6 ∧ p2)) ∨ ((False → False) ∧ (p5 → True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_37 : (((p0 → False) → (True ∨ True)) → ((False → False) ∨ (p7 → False))) := by
      intro assump_10
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    let assump_9 := assump_1 assump_37
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case intro assump_19 assump_20 =>
      have assump_38 : (((p0 → False) → (True ∨ True)) → ((False → False) ∨ (p7 → False))) := by
        intro assump_28
        apply Or.inl
        intro assump_31
        apply False.elim assump_31
      let assump_27 := assump_1 assump_38
      apply False.elim assump_27


variable (p0 p7 p4 p1 p2 p3 : Prop)
theorem file18_57077 : ((((((p1 ∧ p7) → (p4 → p2)) → ((p1 ∨ p3) ∧ (False ∨ p0))) → (((False ∨ False) ∧ (True ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 ∧ p7) → (p4 → p2)) → ((p1 ∨ p3) ∧ (False ∨ p0))) → (((False ∨ False) ∧ (True ∧ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p3 p0 p6 p7 p4 p1 p2 : Prop)
theorem file18_57716 : (((((p4 → False) → (p6 → False)) ∧ ((p1 ∨ p0) → (p0 ∧ p3))) → (((p4 → False) → False) → ((p2 → False) ∨ (p6 ∧ p7)))) → ((((p5 ∨ p7) → False) → ((False → p0) ∨ (p5 ∨ p1))) ∨ (((False → p0) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p7 p5 p6 p3 p2 p0 p1 p4 : Prop)
theorem file18_58105 : (((((False → p3) ∨ (p4 ∨ p0)) → False) ∧ (((False ∧ p5) ∧ (p1 → p6)) → ((p7 → False) ∨ (p2 → p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : ((False → p3) ∨ (p4 ∨ p0)) := by
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p6 p7 p3 p2 p1 p0 p4 p5 : Prop)
theorem file18_58551 : (((((p4 ∨ p4) → False) → ((p1 ∧ False) → False)) ∧ (((True → False) → (p5 ∧ p5)) → ((False → False) → False))) → ((((p0 ∨ p5) ∧ (p5 ∨ p3)) ∨ ((False → p7) → False)) ∧ (((p5 ∧ p6) ∨ (p7 → False)) ∧ ((p2 → p5) → (p3 ∨ p3))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_8
    have assump_94 : ((True → False) → (p5 ∧ p5)) := by
      intro assump_13
      apply And.intro
      have assump_95 : True := by
        apply True.intro
      let assump_16 := assump_13 assump_95
      apply False.elim assump_16
      have assump_96 : True := by
        apply True.intro
      let assump_22 := assump_13 assump_96
      apply False.elim assump_22
    let assump_12 := assump_3 assump_94
    have assump_97 : (False → False) := by
      intro assump_27
      apply False.elim assump_27
    let assump_26 := assump_12 assump_97
    apply False.elim assump_26
  apply And.intro
  cases assump_1
  case intro assump_33 assump_34 =>
    apply Or.inr
    intro assump_39
    have assump_98 : ((True → False) → (p5 ∧ p5)) := by
      intro assump_44
      apply And.intro
      have assump_99 : True := by
        apply True.intro
      let assump_47 := assump_44 assump_99
      apply False.elim assump_47
      have assump_100 : True := by
        apply True.intro
      let assump_53 := assump_44 assump_100
      apply False.elim assump_53
    let assump_43 := assump_34 assump_98
    have assump_101 : (False → False) := by
      intro assump_58
      apply False.elim assump_58
    let assump_57 := assump_43 assump_101
    apply False.elim assump_57
  intro assump_64
  cases assump_1
  case intro assump_67 assump_68 =>
    have assump_102 : ((True → False) → (p5 ∧ p5)) := by
      intro assump_74
      apply And.intro
      have assump_103 : True := by
        apply True.intro
      let assump_77 := assump_74 assump_103
      apply False.elim assump_77
      have assump_104 : True := by
        apply True.intro
      let assump_83 := assump_74 assump_104
      apply False.elim assump_83
    let assump_73 := assump_68 assump_102
    have assump_105 : (False → False) := by
      intro assump_88
      apply False.elim assump_88
    let assump_87 := assump_73 assump_105
    apply False.elim assump_87


variable (p6 p5 p2 : Prop)
theorem file18_60887 : ((((((p6 ∧ p2) ∧ (p6 → False)) ∧ ((True ∨ False) ∨ (True → False))) → (((True ∧ False) → (False → False)) ∧ ((p5 → False) ∨ (False ∨ p2)))) → False) → False) := by
  intro assump_17
  have assump_67 : ((((p6 ∧ p2) ∧ (p6 → False)) ∧ ((True ∨ False) ∨ (True → False))) → (((True ∧ False) → (False → False)) ∧ ((p5 → False) ∨ (False ∨ p2)))) := by
    intro assump_21
    apply And.intro
    intro assump_22
    intro assump_23
    apply False.elim assump_23
    cases assump_21
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_27
          case inl assump_38 =>
            cases assump_38
            case inl assump_40 =>
              apply Or.inl
              intro assump_44
              have assump_68 : p6 := by
                exact assump_30
              let assump_48 := assump_29 assump_68
              apply False.elim assump_48
            case inr assump_41 =>
              apply False.elim assump_41
          case inr assump_39 =>
            apply Or.inl
            intro assump_56
            have assump_69 : True := by
              apply True.intro
            let assump_60 := assump_39 assump_69
            apply False.elim assump_60
  let assump_20 := assump_17 assump_67
  apply False.elim assump_20


variable (p3 p1 p5 p0 p7 : Prop)
theorem file18_62314 : (((((False ∧ p5) ∧ (p0 → False)) → False) → (((p0 ∧ p7) ∧ (True ∨ False)) ∨ ((p3 ∧ p1) → (p3 ∨ p7)))) ∨ ((((p7 → True) → False) ∨ ((True → False) ∨ (p3 ∧ p5))) → (((p0 → p7) → (p7 → False)) ∧ ((p7 → False) ∨ (p0 → p7))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inl
    exact assump_5


variable (p7 p1 p6 p5 p2 p4 : Prop)
theorem file18_62753 : ((((((False ∧ p6) → (False → False)) ∨ ((p5 → p2) → False)) ∨ (((p7 ∧ p6) ∧ (p4 → False)) ∧ ((True ∧ p5) ∧ (p1 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((False ∧ p6) → (False → False)) ∨ ((p5 → p2) → False)) ∨ (((p7 ∧ p6) ∧ (p4 → False)) ∧ ((True ∧ p5) ∧ (p1 → True)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p3 p4 p5 p6 p1 : Prop)
theorem file18_63288 : (((((p6 ∧ False) → (p2 → False)) ∧ ((p4 → False) → (p1 ∨ p3))) → False) → ((((p4 → p4) → (True ∨ p5)) ∨ ((True → False) → False)) ∨ (((True → False) ∧ (p5 ∨ p4)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply Or.inl
  apply True.intro


variable (p7 p0 p3 p1 p4 p5 : Prop)
theorem file18_63625 : (((((p4 ∧ p3) ∨ (p4 ∨ p3)) ∧ ((True → False) ∨ (p4 → False))) ∧ (((p4 → p4) ∨ (False ∧ p7)) → False)) → ((((p5 ∨ p7) ∧ (p4 → False)) → ((p1 → False) ∨ (p4 ∨ False))) → (((p7 ∨ p7) ∨ (p7 ∧ p4)) → ((p5 ∧ p0) ∨ (p5 ∨ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_1
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_15
              case inl assump_24 =>
                have assump_294 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_31
                  exact assump_31
                let assump_30 := assump_13 assump_294
                apply False.elim assump_30
              case inr assump_25 =>
                have assump_295 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_42
                  exact assump_42
                let assump_41 := assump_13 assump_295
                apply False.elim assump_41
          case inr assump_17 =>
            cases assump_17
            case inl assump_48 =>
              cases assump_15
              case inl assump_52 =>
                have assump_296 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_59
                  exact assump_59
                let assump_58 := assump_13 assump_296
                apply False.elim assump_58
              case inr assump_53 =>
                have assump_297 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_70
                  exact assump_70
                let assump_69 := assump_13 assump_297
                apply False.elim assump_69
            case inr assump_49 =>
              cases assump_15
              case inl assump_78 =>
                have assump_298 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_85
                  exact assump_85
                let assump_84 := assump_13 assump_298
                apply False.elim assump_84
              case inr assump_79 =>
                have assump_299 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_96
                  exact assump_96
                let assump_95 := assump_13 assump_299
                apply False.elim assump_95
    case inr assump_7 =>
      cases assump_1
      case intro assump_106 assump_107 =>
        cases assump_106
        case intro assump_108 assump_109 =>
          cases assump_108
          case inl assump_110 =>
            cases assump_110
            case intro assump_112 assump_113 =>
              cases assump_109
              case inl assump_118 =>
                have assump_300 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_125
                  exact assump_125
                let assump_124 := assump_107 assump_300
                apply False.elim assump_124
              case inr assump_119 =>
                have assump_301 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_136
                  exact assump_136
                let assump_135 := assump_107 assump_301
                apply False.elim assump_135
          case inr assump_111 =>
            cases assump_111
            case inl assump_142 =>
              cases assump_109
              case inl assump_146 =>
                have assump_302 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_153
                  exact assump_153
                let assump_152 := assump_107 assump_302
                apply False.elim assump_152
              case inr assump_147 =>
                have assump_303 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_164
                  exact assump_164
                let assump_163 := assump_107 assump_303
                apply False.elim assump_163
            case inr assump_143 =>
              cases assump_109
              case inl assump_172 =>
                have assump_304 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_179
                  exact assump_179
                let assump_178 := assump_107 assump_304
                apply False.elim assump_178
              case inr assump_173 =>
                have assump_305 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_190
                  exact assump_190
                let assump_189 := assump_107 assump_305
                apply False.elim assump_189
  case inr assump_5 =>
    cases assump_5
    case intro assump_196 assump_197 =>
      cases assump_1
      case intro assump_204 assump_205 =>
        cases assump_204
        case intro assump_206 assump_207 =>
          cases assump_206
          case inl assump_208 =>
            cases assump_208
            case intro assump_210 assump_211 =>
              cases assump_207
              case inl assump_216 =>
                have assump_306 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_223
                  exact assump_223
                let assump_222 := assump_205 assump_306
                apply False.elim assump_222
              case inr assump_217 =>
                have assump_307 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_234
                  exact assump_234
                let assump_233 := assump_205 assump_307
                apply False.elim assump_233
          case inr assump_209 =>
            cases assump_209
            case inl assump_240 =>
              cases assump_207
              case inl assump_244 =>
                have assump_308 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_251
                  exact assump_251
                let assump_250 := assump_205 assump_308
                apply False.elim assump_250
              case inr assump_245 =>
                have assump_309 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_262
                  exact assump_262
                let assump_261 := assump_205 assump_309
                apply False.elim assump_261
            case inr assump_241 =>
              cases assump_207
              case inl assump_270 =>
                have assump_310 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_277
                  exact assump_277
                let assump_276 := assump_205 assump_310
                apply False.elim assump_276
              case inr assump_271 =>
                have assump_311 : ((p4 → p4) ∨ (False ∧ p7)) := by
                  apply Or.inl
                  intro assump_288
                  exact assump_288
                let assump_287 := assump_205 assump_311
                apply False.elim assump_287


variable (p3 p0 p2 p4 p5 p7 p1 : Prop)
theorem file18_71077 : (((((False → p4) → False) ∧ ((p5 ∧ p7) ∨ (False ∧ True))) ∧ (((False ∧ p4) ∧ (p2 ∧ p1)) → ((p0 → False) → (p7 ∨ p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_32 : (False → p4) := by
            intro assump_22
            apply False.elim assump_22
          let assump_21 := assump_4 assump_32
          apply False.elim assump_21
      case inr assump_9 =>
        cases assump_9
        case intro assump_28 assump_29 =>
          apply False.elim assump_28


variable (p1 : Prop)
theorem file18_71817 : (((((p1 → False) ∧ (False ∧ p1)) → False) → False) → False) := by
  intro assump_18
  have assump_34 : (((p1 → False) ∧ (False ∧ p1)) → False) := by
    intro assump_22
    cases assump_22
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        apply False.elim assump_27
  let assump_21 := assump_18 assump_34
  apply False.elim assump_21


variable (p4 p7 p6 p0 p1 p2 p5 p3 : Prop)
theorem file18_72275 : (((((p2 ∨ p5) ∧ (p0 → p2)) ∨ ((p7 → False) ∧ (p6 ∨ False))) ∨ (((p3 → p7) ∧ (p4 ∨ p2)) ∧ ((p1 ∧ p2) → False))) → ((((p3 ∨ p0) ∧ (p0 → p1)) ∨ ((False ∧ p4) → (p0 ∧ p2))) ∧ (((p7 ∨ p6) ∨ (p1 → True)) ∨ ((p0 → p1) ∧ (p2 ∨ p5))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inr
          intro assump_14
          apply And.intro
          cases assump_14
          case intro assump_15 assump_16 =>
            apply False.elim assump_15
          cases assump_14
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
        case inr assump_9 =>
          apply Or.inr
          intro assump_27
          apply And.intro
          cases assump_27
          case intro assump_28 assump_29 =>
            apply False.elim assump_28
          cases assump_27
          case intro assump_32 assump_33 =>
            apply False.elim assump_32
    case inr assump_5 =>
      cases assump_5
      case intro assump_36 assump_37 =>
        cases assump_37
        case inl assump_40 =>
          apply Or.inr
          intro assump_44
          apply And.intro
          cases assump_44
          case intro assump_45 assump_46 =>
            apply False.elim assump_45
          cases assump_44
          case intro assump_49 assump_50 =>
            apply False.elim assump_49
        case inr assump_41 =>
          apply False.elim assump_41
  case inr assump_3 =>
    cases assump_3
    case intro assump_55 assump_56 =>
      cases assump_55
      case intro assump_57 assump_58 =>
        cases assump_58
        case inl assump_61 =>
          apply Or.inr
          intro assump_67
          apply And.intro
          cases assump_67
          case intro assump_68 assump_69 =>
            apply False.elim assump_68
          cases assump_67
          case intro assump_72 assump_73 =>
            apply False.elim assump_72
        case inr assump_62 =>
          apply Or.inr
          intro assump_80
          apply And.intro
          cases assump_80
          case intro assump_81 assump_82 =>
            apply False.elim assump_81
          cases assump_80
          case intro assump_85 assump_86 =>
            apply False.elim assump_85
  cases assump_1
  case inl assump_89 =>
    cases assump_89
    case inl assump_91 =>
      cases assump_91
      case intro assump_93 assump_94 =>
        cases assump_93
        case inl assump_95 =>
          apply Or.inl
          apply Or.inr
          intro assump_101
          apply True.intro
        case inr assump_96 =>
          apply Or.inl
          apply Or.inr
          intro assump_106
          apply True.intro
    case inr assump_92 =>
      cases assump_92
      case intro assump_107 assump_108 =>
        cases assump_108
        case inl assump_111 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          exact assump_111
        case inr assump_112 =>
          apply False.elim assump_112
  case inr assump_90 =>
    cases assump_90
    case intro assump_117 assump_118 =>
      cases assump_117
      case intro assump_119 assump_120 =>
        cases assump_120
        case inl assump_123 =>
          apply Or.inl
          apply Or.inr
          intro assump_129
          apply True.intro
        case inr assump_124 =>
          apply Or.inl
          apply Or.inr
          intro assump_134
          apply True.intro


variable (p2 p1 p3 p6 p5 p7 p4 : Prop)
theorem file18_75908 : ((((((p5 ∧ p3) ∧ (p5 → p4)) ∧ ((p4 ∧ False) ∧ (p7 ∧ p1))) ∧ (((p3 → False) → False) ∧ ((p1 → False) ∧ (p2 → False)))) ∧ ((((p4 ∧ p7) → False) ∨ ((p6 ∧ p7) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_21


variable (p2 p7 p3 p0 p1 p5 p6 : Prop)
theorem file18_76669 : (((((p6 ∨ p7) ∨ (p3 → p7)) ∨ ((p5 ∧ p7) → (p2 → False))) ∧ (((p3 ∨ p1) ∨ (True ∧ True)) → False)) → ((((True → False) → False) ∧ ((False → False) ∨ (p0 → False))) ∧ (((p0 ∧ p2) → (p1 → False)) ∧ ((p6 → p7) ∧ (True ∨ p5))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case inl assump_11 =>
          have assump_194 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
            apply Or.inr
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_17 := assump_6 assump_194
          apply False.elim assump_17
        case inr assump_12 =>
          have assump_195 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
            apply Or.inr
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_25 := assump_6 assump_195
          apply False.elim assump_25
      case inr assump_10 =>
        have assump_196 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
          apply Or.inr
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_33 := assump_6 assump_196
        apply False.elim assump_33
    case inr assump_8 =>
      have assump_197 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
        apply Or.inr
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_41 := assump_6 assump_197
      apply False.elim assump_41
  cases assump_1
  case intro assump_45 assump_46 =>
    cases assump_45
    case inl assump_47 =>
      cases assump_47
      case inl assump_49 =>
        cases assump_49
        case inl assump_51 =>
          apply Or.inl
          intro assump_57
          apply False.elim assump_57
        case inr assump_52 =>
          apply Or.inl
          intro assump_64
          apply False.elim assump_64
      case inr assump_50 =>
        apply Or.inl
        intro assump_71
        apply False.elim assump_71
    case inr assump_48 =>
      apply Or.inl
      intro assump_78
      apply False.elim assump_78
  apply And.intro
  intro assump_81
  intro assump_82
  cases assump_81
  case intro assump_85 assump_86 =>
    cases assump_1
    case intro assump_91 assump_92 =>
      cases assump_91
      case inl assump_93 =>
        cases assump_93
        case inl assump_95 =>
          cases assump_95
          case inl assump_97 =>
            have assump_198 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
              apply Or.inl
              apply Or.inr
              exact assump_82
            let assump_103 := assump_92 assump_198
            apply False.elim assump_103
          case inr assump_98 =>
            have assump_199 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
              apply Or.inl
              apply Or.inr
              exact assump_82
            let assump_111 := assump_92 assump_199
            apply False.elim assump_111
        case inr assump_96 =>
          have assump_200 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
            apply Or.inl
            apply Or.inr
            exact assump_82
          let assump_119 := assump_92 assump_200
          apply False.elim assump_119
      case inr assump_94 =>
        have assump_201 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
          apply Or.inl
          apply Or.inr
          exact assump_82
        let assump_127 := assump_92 assump_201
        apply False.elim assump_127
  apply And.intro
  intro assump_131
  cases assump_1
  case intro assump_134 assump_135 =>
    cases assump_134
    case inl assump_136 =>
      cases assump_136
      case inl assump_138 =>
        cases assump_138
        case inl assump_140 =>
          have assump_202 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
            apply Or.inr
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_146 := assump_135 assump_202
          apply False.elim assump_146
        case inr assump_141 =>
          exact assump_141
      case inr assump_139 =>
        have assump_203 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
          apply Or.inr
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_158 := assump_135 assump_203
        apply False.elim assump_158
    case inr assump_137 =>
      have assump_204 : ((p3 ∨ p1) ∨ (True ∧ True)) := by
        apply Or.inr
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_166 := assump_135 assump_204
      apply False.elim assump_166
  cases assump_1
  case intro assump_170 assump_171 =>
    cases assump_170
    case inl assump_172 =>
      cases assump_172
      case inl assump_174 =>
        cases assump_174
        case inl assump_176 =>
          apply Or.inl
          apply True.intro
        case inr assump_177 =>
          apply Or.inl
          apply True.intro
      case inr assump_175 =>
        apply Or.inl
        apply True.intro
    case inr assump_173 =>
      apply Or.inl
      apply True.intro


variable (p6 p1 p3 p0 p4 p5 : Prop)
theorem file18_81833 : ((((((p4 → False) → False) → False) ∨ (((True → True) → False) ∧ ((p1 ∧ p1) ∨ (True ∨ p5)))) ∧ ((((p4 ∨ p3) ∨ (p0 ∨ False)) → ((p6 → True) → False)) ∧ (((p0 → True) ∨ (p6 → p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_70 : ((p0 → True) ∨ (p6 → p1)) := by
          apply Or.inl
          intro assump_15
          apply True.intro
        let assump_14 := assump_9 assump_70
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case intro assump_19 assump_20 =>
        cases assump_20
        case inl assump_23 =>
          cases assump_23
          case intro assump_25 assump_26 =>
            cases assump_3
            case intro assump_31 assump_32 =>
              have assump_71 : ((p0 → True) ∨ (p6 → p1)) := by
                apply Or.inl
                intro assump_38
                apply True.intro
              let assump_37 := assump_32 assump_71
              apply False.elim assump_37
        case inr assump_24 =>
          cases assump_24
          case inl assump_42 =>
            cases assump_3
            case intro assump_46 assump_47 =>
              have assump_72 : ((p0 → True) ∨ (p6 → p1)) := by
                apply Or.inl
                intro assump_53
                apply True.intro
              let assump_52 := assump_47 assump_72
              apply False.elim assump_52
          case inr assump_43 =>
            cases assump_3
            case intro assump_59 assump_60 =>
              have assump_73 : ((p0 → True) ∨ (p6 → p1)) := by
                apply Or.inl
                intro assump_66
                apply True.intro
              let assump_65 := assump_60 assump_73
              apply False.elim assump_65


variable (p7 p4 p1 p2 : Prop)
theorem file18_83770 : ((((((p7 → False) → False) → False) ∨ (((p1 ∧ p2) ∨ (p2 ∨ p1)) → False)) ∧ ((((p4 ∧ p2) ∧ (p2 ∧ False)) → False) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      have assump_56 : (((p4 ∧ p2) ∧ (p2 ∧ False)) → False) := by
        intro assump_15
        cases assump_15
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_17
            case intro assump_24 assump_25 =>
              apply False.elim assump_25
      let assump_14 := assump_7 assump_56
      apply False.elim assump_14
    case inr assump_9 =>
      have assump_57 : (((p4 ∧ p2) ∧ (p2 ∧ False)) → False) := by
        intro assump_38
        cases assump_38
        case intro assump_39 assump_40 =>
          cases assump_39
          case intro assump_41 assump_42 =>
            cases assump_40
            case intro assump_47 assump_48 =>
              apply False.elim assump_48
      let assump_37 := assump_7 assump_57
      apply False.elim assump_37


variable (p3 p2 p4 p5 p7 : Prop)
theorem file18_84934 : ((((((True → p4) → False) → False) ∨ (((p2 → False) ∧ (True ∧ p5)) ∨ ((p5 ∧ p3) ∧ (p7 ∨ p7)))) ∧ ((((p5 → p4) → False) → ((False → False) ∨ (p5 ∨ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_82 : (((p5 → p4) → False) → ((False → False) ∨ (p5 ∨ p4))) := by
        intro assump_11
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
      let assump_10 := assump_3 assump_82
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_20 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          cases assump_23
          case intro assump_26 assump_27 =>
            have assump_83 : (((p5 → p4) → False) → ((False → False) ∨ (p5 ∨ p4))) := by
              intro assump_35
              apply Or.inl
              intro assump_38
              apply False.elim assump_38
            let assump_34 := assump_3 assump_83
            apply False.elim assump_34
      case inr assump_21 =>
        cases assump_21
        case intro assump_44 assump_45 =>
          cases assump_44
          case intro assump_46 assump_47 =>
            cases assump_45
            case inl assump_52 =>
              have assump_84 : (((p5 → p4) → False) → ((False → False) ∨ (p5 ∨ p4))) := by
                intro assump_59
                apply Or.inl
                intro assump_62
                apply False.elim assump_62
              let assump_58 := assump_3 assump_84
              apply False.elim assump_58
            case inr assump_53 =>
              have assump_85 : (((p5 → p4) → False) → ((False → False) ∨ (p5 ∨ p4))) := by
                intro assump_73
                apply Or.inl
                intro assump_76
                apply False.elim assump_76
              let assump_72 := assump_3 assump_85
              apply False.elim assump_72


variable (p7 p3 p5 p0 p4 : Prop)
theorem file18_86952 : (((((p5 → p0) ∧ (p4 ∧ p3)) ∧ ((False → p5) → (p4 ∨ p5))) ∧ (((False ∨ False) → (p0 ∧ p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          have assump_37 : ((False ∨ False) → (p0 ∧ p7)) := by
            intro assump_21
            apply And.intro
            cases assump_21
            case inl assump_22 =>
              apply False.elim assump_22
            case inr assump_23 =>
              apply False.elim assump_23
            cases assump_21
            case inl assump_28 =>
              apply False.elim assump_28
            case inr assump_29 =>
              apply False.elim assump_29
          let assump_20 := assump_3 assump_37
          apply False.elim assump_20


variable (p1 p4 p7 p2 p5 : Prop)
theorem file18_87929 : ((((((False → False) → (True ∨ False)) ∨ ((p2 → p1) ∧ (p4 → p5))) ∨ (((p7 ∨ p7) ∨ (False ∨ True)) ∨ ((p7 → p7) ∧ (p4 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) → (True ∨ False)) ∨ ((p2 → p1) ∧ (p4 → p5))) ∨ (((p7 ∨ p7) ∨ (False ∨ True)) ∨ ((p7 → p7) ∧ (p4 ∧ p7)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p2 p0 p6 p5 p1 : Prop)
theorem file18_88461 : (((((p3 ∨ p5) → (p0 → False)) → ((False → False) ∨ (p6 ∨ p2))) → False) → ((((p6 ∧ p2) → False) ∧ ((p1 ∨ p3) → False)) ∨ (((False → False) → False) ∨ ((p1 ∨ False) ∧ (True → p3))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_52 : (((p3 ∨ p5) → (p0 → False)) → ((False → False) ∨ (p6 ∨ p2))) := by
      intro assump_14
      apply Or.inl
      intro assump_17
      apply False.elim assump_17
    let assump_13 := assump_1 assump_52
    apply False.elim assump_13
  intro assump_23
  cases assump_23
  case inl assump_24 =>
    have assump_53 : (((p3 ∨ p5) → (p0 → False)) → ((False → False) ∨ (p6 ∨ p2))) := by
      intro assump_30
      apply Or.inl
      intro assump_33
      apply False.elim assump_33
    let assump_29 := assump_1 assump_53
    apply False.elim assump_29
  case inr assump_25 =>
    have assump_54 : (((p3 ∨ p5) → (p0 → False)) → ((False → False) ∨ (p6 ∨ p2))) := by
      intro assump_43
      apply Or.inl
      intro assump_46
      apply False.elim assump_46
    let assump_42 := assump_1 assump_54
    apply False.elim assump_42


variable (p6 p4 p1 p0 p3 p5 : Prop)
theorem file18_89676 : (((((p6 → False) ∧ (p4 → True)) → ((p4 ∧ p3) → False)) → False) → ((((p1 ∨ p3) → (False → False)) ∧ ((True ∨ True) ∧ (False → p1))) → (((p3 → False) → (p6 → p3)) ∨ ((p0 ∧ p5) → (p1 → p0))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        intro assump_17
        intro assump_18
        have assump_87 : (((p6 → False) ∧ (p4 → True)) → ((p4 ∧ p3) → False)) := by
          intro assump_26
          intro assump_27
          cases assump_27
          case intro assump_28 assump_29 =>
            cases assump_26
            case intro assump_34 assump_35 =>
              have assump_88 : p6 := by
                exact assump_18
              let assump_42 := assump_34 assump_88
              apply False.elim assump_42
        let assump_25 := assump_1 assump_87
        apply False.elim assump_25
      case inr assump_10 =>
        apply Or.inl
        intro assump_55
        intro assump_56
        have assump_89 : (((p6 → False) ∧ (p4 → True)) → ((p4 ∧ p3) → False)) := by
          intro assump_64
          intro assump_65
          cases assump_65
          case intro assump_66 assump_67 =>
            cases assump_64
            case intro assump_72 assump_73 =>
              have assump_90 : p6 := by
                exact assump_56
              let assump_80 := assump_72 assump_90
              apply False.elim assump_80
        let assump_63 := assump_1 assump_89
        apply False.elim assump_63


variable (p1 p3 p5 p6 p2 p7 p0 : Prop)
theorem file18_91336 : (((((p0 ∧ True) → False) → False) → (((False → p5) ∨ (p1 ∧ p7)) ∨ ((p2 ∨ p6) → (p3 ∨ p3)))) ∨ ((((p7 → False) ∧ (True ∧ p1)) ∨ ((p3 → False) → (p1 → False))) ∧ (((p7 ∧ p7) ∧ (p0 → False)) → False))) := by
  apply Or.inl
  intro assump_11
  apply Or.inl
  apply Or.inl
  intro assump_14
  apply False.elim assump_14


variable (p3 p6 p7 p2 p4 p5 : Prop)
theorem file18_91711 : ((((((p4 ∧ p2) → False) → ((p7 → False) → False)) ∨ (((p5 ∨ p5) → (True → p3)) ∧ ((p2 → False) → False))) ∧ ((((p7 ∨ p2) ∨ (p5 ∨ p4)) → False) ∨ (((p6 → p2) ∧ (p5 ∧ False)) ∧ ((p6 ∨ p2) ∧ (p6 → p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        have assump_86 : ((p4 ∧ p2) → False) := by
          intro assump_14
          cases assump_14
          case intro assump_15 assump_16 =>
            have assump_87 : ((p7 ∨ p2) ∨ (p5 ∨ p4)) := by
              apply Or.inl
              apply Or.inr
              exact assump_16
            let assump_23 := assump_8 assump_87
            apply False.elim assump_23
        let assump_13 := assump_4 assump_86
        have assump_88 : (p7 → False) := by
          intro assump_28
          have assump_89 : ((p7 ∨ p2) ∨ (p5 ∨ p4)) := by
            apply Or.inl
            apply Or.inl
            exact assump_28
          let assump_32 := assump_8 assump_89
          apply False.elim assump_32
        let assump_27 := assump_13 assump_88
        apply False.elim assump_27
      case inr assump_9 =>
        cases assump_9
        case intro assump_39 assump_40 =>
          cases assump_39
          case intro assump_41 assump_42 =>
            cases assump_42
            case intro assump_45 assump_46 =>
              apply False.elim assump_46
    case inr assump_5 =>
      cases assump_5
      case intro assump_51 assump_52 =>
        cases assump_3
        case inl assump_57 =>
          have assump_90 : (p2 → False) := by
            intro assump_63
            have assump_91 : ((p7 ∨ p2) ∨ (p5 ∨ p4)) := by
              apply Or.inl
              apply Or.inr
              exact assump_63
            let assump_67 := assump_57 assump_91
            apply False.elim assump_67
          let assump_62 := assump_52 assump_90
          apply False.elim assump_62
        case inr assump_58 =>
          cases assump_58
          case intro assump_74 assump_75 =>
            cases assump_74
            case intro assump_76 assump_77 =>
              cases assump_77
              case intro assump_80 assump_81 =>
                apply False.elim assump_81


variable (p4 p7 p5 p3 p2 p0 : Prop)
theorem file18_94037 : (((((p2 → False) → (p4 ∧ p0)) → False) → (((p2 ∧ p7) ∨ (p0 → True)) ∨ ((p3 → False) ∨ (p4 ∧ False)))) ∨ ((((p5 → False) → (p7 ∨ p4)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply True.intro


variable (p3 p2 p5 p1 p6 p7 p4 : Prop)
theorem file18_94356 : (((((p7 ∧ p4) ∧ (False ∧ p5)) ∧ ((p6 → p1) ∨ (p7 ∨ p3))) → (((False → p2) → False) → ((True → p7) → False))) ∨ ((((p4 → True) ∧ (p5 ∧ False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          apply False.elim assump_18


variable (p4 p5 p3 p6 p1 : Prop)
theorem file18_94919 : (((((True ∨ p6) → False) → ((p5 → p1) → (p4 ∧ p3))) → False) → False) := by
  intro assump_19
  have assump_44 : (((True ∨ p6) → False) → ((p5 → p1) → (p4 ∧ p3))) := by
    intro assump_23
    intro assump_24
    apply And.intro
    have assump_45 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_29 := assump_23 assump_45
    apply False.elim assump_29
    have assump_46 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_37 := assump_23 assump_46
    apply False.elim assump_37
  let assump_22 := assump_19 assump_44
  apply False.elim assump_22


variable (p5 p2 p3 p1 p4 p0 p7 p6 : Prop)
theorem file18_95588 : (((((p7 → False) ∧ (p3 ∧ p7)) ∧ ((p6 → False) ∨ (p1 → False))) → False) ∨ ((((p2 → True) → (True ∨ p3)) ∨ ((p1 ∧ p0) ∨ (p4 → p2))) ∧ (((False → p1) ∨ (p6 ∧ p5)) → ((p6 → False) ∧ (p3 ∧ p3))))) := by
  apply Or.inl
  intro assump_27
  cases assump_27
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      cases assump_31
      case intro assump_34 assump_35 =>
        cases assump_29
        case inl assump_40 =>
          have assump_60 : p7 := by
            exact assump_35
          let assump_47 := assump_30 assump_60
          apply False.elim assump_47
        case inr assump_41 =>
          have assump_61 : p7 := by
            exact assump_35
          let assump_56 := assump_30 assump_61
          apply False.elim assump_56


variable (p1 p0 p2 p7 p5 p4 p3 : Prop)
theorem file18_96437 : (((((True ∧ p4) → (p1 ∨ p2)) → ((False ∧ p0) → False)) ∧ (((True → False) ∧ (p2 → p3)) → ((p2 → False) ∧ (p0 → False)))) ∨ ((((p5 ∧ p0) ∧ (p7 → False)) ∧ ((p4 ∨ p1) ∨ (p2 → False))) ∧ (((p1 → p3) → (False → False)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3
  intro assump_7
  apply And.intro
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    have assump_37 : True := by
      apply True.intro
    let assump_19 := assump_11 assump_37
    apply False.elim assump_19
  intro assump_23
  cases assump_7
  case intro assump_26 assump_27 =>
    have assump_38 : True := by
      apply True.intro
    let assump_33 := assump_26 assump_38
    apply False.elim assump_33


variable (p4 p3 p7 p6 p0 p1 p2 : Prop)
theorem file18_97310 : (((((p3 ∨ p1) ∨ (True → False)) ∨ ((p1 ∨ True) ∧ (p2 → False))) → (((False ∧ p2) → (p4 ∨ p2)) ∨ ((True ∨ p3) ∨ (p1 ∧ p6)))) ∨ ((((True ∨ p2) ∨ (p3 ∧ p0)) ∨ ((p2 ∧ p7) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_10
        cases assump_10
        case intro assump_11 assump_12 =>
          apply False.elim assump_11
      case inr assump_7 =>
        apply Or.inl
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
    case inr assump_5 =>
      apply Or.inl
      intro assump_24
      cases assump_24
      case intro assump_25 assump_26 =>
        apply False.elim assump_25
  case inr assump_3 =>
    cases assump_3
    case intro assump_29 assump_30 =>
      cases assump_29
      case inl assump_31 =>
        apply Or.inl
        intro assump_37
        cases assump_37
        case intro assump_38 assump_39 =>
          apply False.elim assump_38
      case inr assump_32 =>
        apply Or.inl
        intro assump_46
        cases assump_46
        case intro assump_47 assump_48 =>
          apply False.elim assump_47


variable (p2 p4 p3 p7 p6 p0 : Prop)
theorem file18_98667 : (((((p3 ∧ False) → (p7 ∧ p6)) ∨ ((p6 → p2) → False)) → False) → ((((p4 ∨ p0) ∧ (p2 ∨ p3)) → ((p4 ∧ p7) ∧ (p3 ∧ p4))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_24 : (((p3 ∧ False) → (p7 ∧ p6)) ∨ ((p6 → p2) → False)) := by
    apply Or.inl
    intro assump_8
    apply And.intro
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
    cases assump_8
    case intro assump_15 assump_16 =>
      apply False.elim assump_16
  let assump_7 := assump_1 assump_24
  apply False.elim assump_7


variable (p0 p1 p4 p7 p2 p5 : Prop)
theorem file18_99270 : (((((False → False) → False) ∧ ((True ∨ p1) ∨ (p7 ∨ False))) → False) ∨ ((((p1 → p2) → False) → ((p0 ∨ p5) → (True → True))) ∨ (((p4 → False) → False) ∨ ((p0 → False) → (p4 → p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_43 : (False → False) := by
          intro assump_13
          apply False.elim assump_13
        let assump_12 := assump_2 assump_43
        apply False.elim assump_12
      case inr assump_9 =>
        have assump_44 : (False → False) := by
          intro assump_23
          apply False.elim assump_23
        let assump_22 := assump_2 assump_44
        apply False.elim assump_22
    case inr assump_7 =>
      cases assump_7
      case inl assump_29 =>
        have assump_45 : (False → False) := by
          intro assump_35
          apply False.elim assump_35
        let assump_34 := assump_2 assump_45
        apply False.elim assump_34
      case inr assump_30 =>
        apply False.elim assump_30


variable (p5 p3 p7 p6 p4 p1 p0 : Prop)
theorem file18_100428 : (((((p3 ∨ p5) ∨ (True ∨ p4)) → False) → (((p6 ∨ p0) ∧ (p6 ∧ p1)) ∧ ((p1 → False) ∨ (p6 ∧ p4)))) ∨ ((((p4 ∧ p7) → False) → ((p3 → False) → (p1 ∨ False))) ∧ (((p7 ∧ p0) ∧ (p6 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  have assump_30 : ((p3 ∨ p5) ∨ (True ∨ p4)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4
  apply And.intro
  have assump_31 : ((p3 ∨ p5) ∨ (True ∨ p4)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_10 := assump_1 assump_31
  apply False.elim assump_10
  have assump_32 : ((p3 ∨ p5) ∨ (True ∨ p4)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_16 := assump_1 assump_32
  apply False.elim assump_16
  apply Or.inl
  intro assump_22
  have assump_33 : ((p3 ∨ p5) ∨ (True ∨ p4)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_26 := assump_1 assump_33
  apply False.elim assump_26


variable (p6 p1 p7 p0 p3 p4 p5 : Prop)
theorem file18_101500 : (((((p6 → p0) → (p0 → p4)) → ((p5 ∨ p5) → False)) → False) → ((((p4 ∧ p7) ∧ (p0 ∧ True)) → ((p7 ∧ p3) ∨ (p0 ∧ True))) ∨ (((p1 → p5) → (True ∨ True)) ∧ ((p3 → p5) ∨ (False → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case intro assump_13 assump_14 =>
        apply Or.inr
        apply And.intro
        exact assump_13
        apply True.intro


variable (p4 p2 p0 p5 : Prop)
theorem file18_102054 : (((((p2 → p4) → False) → ((p5 ∨ p5) → (p0 ∨ True))) → False) → False) := by
  intro assump_10
  have assump_29 : (((p2 → p4) → False) → ((p5 ∨ p5) → (p0 ∨ True))) := by
    intro assump_14
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      apply Or.inr
      apply True.intro
    case inr assump_17 =>
      apply Or.inr
      apply True.intro
  let assump_13 := assump_10 assump_29
  apply False.elim assump_13


variable (p6 p5 p0 p7 p3 p2 : Prop)
theorem file18_102547 : (((((True ∨ p2) ∧ (p3 ∧ p5)) ∧ ((p7 ∧ p6) ∧ (p5 ∨ p0))) ∧ (((False → False) → False) ∨ ((p3 → True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case intro assump_12 assump_13 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_19
                case inl assump_26 =>
                  cases assump_3
                  case inl assump_30 =>
                    have assump_126 : (False → False) := by
                      intro assump_35
                      apply False.elim assump_35
                    let assump_34 := assump_30 assump_126
                    apply False.elim assump_34
                  case inr assump_31 =>
                    have assump_127 : (p3 → True) := by
                      intro assump_44
                      apply True.intro
                    let assump_43 := assump_31 assump_127
                    apply False.elim assump_43
                case inr assump_27 =>
                  cases assump_3
                  case inl assump_50 =>
                    have assump_128 : (False → False) := by
                      intro assump_55
                      apply False.elim assump_55
                    let assump_54 := assump_50 assump_128
                    apply False.elim assump_54
                  case inr assump_51 =>
                    have assump_129 : (p3 → True) := by
                      intro assump_64
                      apply True.intro
                    let assump_63 := assump_51 assump_129
                    apply False.elim assump_63
        case inr assump_9 =>
          cases assump_7
          case intro assump_70 assump_71 =>
            cases assump_5
            case intro assump_76 assump_77 =>
              cases assump_76
              case intro assump_78 assump_79 =>
                cases assump_77
                case inl assump_84 =>
                  cases assump_3
                  case inl assump_88 =>
                    have assump_130 : (False → False) := by
                      intro assump_93
                      apply False.elim assump_93
                    let assump_92 := assump_88 assump_130
                    apply False.elim assump_92
                  case inr assump_89 =>
                    have assump_131 : (p3 → True) := by
                      intro assump_102
                      apply True.intro
                    let assump_101 := assump_89 assump_131
                    apply False.elim assump_101
                case inr assump_85 =>
                  cases assump_3
                  case inl assump_108 =>
                    have assump_132 : (False → False) := by
                      intro assump_113
                      apply False.elim assump_113
                    let assump_112 := assump_108 assump_132
                    apply False.elim assump_112
                  case inr assump_109 =>
                    have assump_133 : (p3 → True) := by
                      intro assump_122
                      apply True.intro
                    let assump_121 := assump_109 assump_133
                    apply False.elim assump_121


variable (p2 p1 p6 p7 p5 p0 : Prop)
theorem file18_106078 : (((((p0 ∧ p7) ∧ (p5 → True)) ∧ ((p1 ∧ False) ∧ (True → p6))) ∧ (((p2 → False) ∧ (False ∨ False)) ∨ ((True → False) → (p7 ∨ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_5
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply False.elim assump_19


variable (p6 p5 p1 p0 p4 : Prop)
theorem file18_106709 : ((((((p1 ∨ p5) ∨ (False ∨ p5)) ∧ ((p6 ∧ True) → (p4 ∧ p1))) ∨ (((p4 → False) ∧ (False ∨ p0)) → False)) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            have assump_94 : (((False → False) → False) → False) := by
              intro assump_19
              have assump_95 : (False → False) := by
                intro assump_23
                apply False.elim assump_23
              let assump_22 := assump_19 assump_95
              apply False.elim assump_22
            let assump_18 := assump_3 assump_94
            apply False.elim assump_18
          case inr assump_11 =>
            have assump_96 : (((False → False) → False) → False) := by
              intro assump_39
              have assump_97 : (False → False) := by
                intro assump_43
                apply False.elim assump_43
              let assump_42 := assump_39 assump_97
              apply False.elim assump_42
            let assump_38 := assump_3 assump_96
            apply False.elim assump_38
        case inr assump_9 =>
          cases assump_9
          case inl assump_52 =>
            apply False.elim assump_52
          case inr assump_53 =>
            have assump_98 : (((False → False) → False) → False) := by
              intro assump_63
              have assump_99 : (False → False) := by
                intro assump_67
                apply False.elim assump_67
              let assump_66 := assump_63 assump_99
              apply False.elim assump_66
            let assump_62 := assump_3 assump_98
            apply False.elim assump_62
    case inr assump_5 =>
      have assump_100 : (((False → False) → False) → False) := by
        intro assump_81
        have assump_101 : (False → False) := by
          intro assump_85
          apply False.elim assump_85
        let assump_84 := assump_81 assump_101
        apply False.elim assump_84
      let assump_80 := assump_3 assump_100
      apply False.elim assump_80


variable (p7 p0 : Prop)
theorem file18_109000 : ((((((True → p0) → (p7 → p7)) → False) → False) → False) → False) := by
  intro assump_24
  have assump_44 : ((((True → p0) → (p7 → p7)) → False) → False) := by
    intro assump_28
    have assump_45 : ((True → p0) → (p7 → p7)) := by
      intro assump_32
      intro assump_33
      exact assump_33
    let assump_31 := assump_28 assump_45
    apply False.elim assump_31
  let assump_27 := assump_24 assump_44
  apply False.elim assump_27


variable (p0 p4 p1 p6 p7 : Prop)
theorem file18_109497 : ((((((p4 ∨ p7) ∨ (p1 → p6)) → ((True ∨ p0) ∨ (p1 ∨ False))) ∨ (((p7 → False) → (p6 → False)) ∨ ((p6 ∧ True) ∧ (p0 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p4 ∨ p7) ∨ (p1 → p6)) → ((True ∨ p0) ∨ (p1 ∨ False))) ∨ (((p7 → False) → (p6 → False)) ∨ ((p6 ∧ True) ∧ (p0 ∨ p4)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_9 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p0 p5 p7 p2 p4 : Prop)
theorem file18_110307 : (((((p0 ∧ p4) → (True → False)) ∧ ((p2 → p0) → False)) ∧ (((p7 ∨ p0) ∨ (False → False)) ∧ ((p7 ∧ p0) ∧ (p1 ∨ p7)))) → ((((p5 ∨ True) → (True → False)) → False) ∨ (((p0 ∧ p7) ∨ (p1 → True)) ∧ ((p7 ∨ p4) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_11
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_19
                case inl assump_26 =>
                  apply Or.inl
                  intro assump_30
                  have assump_112 : (p5 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_33 := assump_30 assump_112
                  have assump_113 : True := by
                    apply True.intro
                  let assump_34 := assump_33 assump_113
                  apply False.elim assump_34
                case inr assump_27 =>
                  apply Or.inl
                  intro assump_40
                  have assump_114 : (p5 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_43 := assump_40 assump_114
                  have assump_115 : True := by
                    apply True.intro
                  let assump_44 := assump_43 assump_115
                  apply False.elim assump_44
          case inr assump_15 =>
            cases assump_11
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_51
                case inl assump_58 =>
                  apply Or.inl
                  intro assump_62
                  have assump_116 : (p5 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_65 := assump_62 assump_116
                  have assump_117 : True := by
                    apply True.intro
                  let assump_66 := assump_65 assump_117
                  apply False.elim assump_66
                case inr assump_59 =>
                  apply Or.inl
                  intro assump_72
                  have assump_118 : (p5 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_75 := assump_72 assump_118
                  have assump_119 : True := by
                    apply True.intro
                  let assump_76 := assump_75 assump_119
                  apply False.elim assump_76
        case inr assump_13 =>
          cases assump_11
          case intro assump_82 assump_83 =>
            cases assump_82
            case intro assump_84 assump_85 =>
              cases assump_83
              case inl assump_90 =>
                apply Or.inl
                intro assump_94
                have assump_120 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_97 := assump_94 assump_120
                have assump_121 : True := by
                  apply True.intro
                let assump_98 := assump_97 assump_121
                apply False.elim assump_98
              case inr assump_91 =>
                apply Or.inl
                intro assump_104
                have assump_122 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_107 := assump_104 assump_122
                have assump_123 : True := by
                  apply True.intro
                let assump_108 := assump_107 assump_123
                apply False.elim assump_108


variable (p2 p4 p5 p6 p3 p0 p7 p1 : Prop)
theorem file18_114263 : (((((False → p4) ∧ (p2 ∨ p1)) → ((p4 → False) → False)) → (((p1 ∧ False) ∧ (p2 → False)) → ((p0 → p6) → (p6 → False)))) ∨ ((((p3 ∨ p7) ∧ (p4 ∨ p5)) ∨ ((p3 ∧ p2) → (False → False))) ∧ (((p3 → p1) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      apply False.elim assump_12


variable (p4 p3 p1 p2 p5 p7 : Prop)
theorem file18_114769 : ((((((False ∧ p1) → (p7 ∧ p4)) → False) → (((p4 → p2) ∨ (p7 → False)) ∧ ((p3 ∧ p5) ∧ (p5 → p5)))) → False) → False) := by
  intro assump_1
  have assump_63 : ((((False ∧ p1) → (p7 ∧ p4)) → False) → (((p4 → p2) ∨ (p7 → False)) ∧ ((p3 ∧ p5) ∧ (p5 → p5)))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    intro assump_8
    have assump_64 : ((False ∧ p1) → (p7 ∧ p4)) := by
      intro assump_13
      apply And.intro
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
      cases assump_13
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
    let assump_12 := assump_5 assump_64
    apply False.elim assump_12
    apply And.intro
    apply And.intro
    have assump_65 : ((False ∧ p1) → (p7 ∧ p4)) := by
      intro assump_28
      apply And.intro
      cases assump_28
      case intro assump_29 assump_30 =>
        apply False.elim assump_29
      cases assump_28
      case intro assump_33 assump_34 =>
        apply False.elim assump_33
    let assump_27 := assump_5 assump_65
    apply False.elim assump_27
    have assump_66 : ((False ∧ p1) → (p7 ∧ p4)) := by
      intro assump_43
      apply And.intro
      cases assump_43
      case intro assump_44 assump_45 =>
        apply False.elim assump_44
      cases assump_43
      case intro assump_48 assump_49 =>
        apply False.elim assump_48
    let assump_42 := assump_5 assump_66
    apply False.elim assump_42
    intro assump_55
    exact assump_55
  let assump_4 := assump_1 assump_63
  apply False.elim assump_4


variable (p7 p1 p2 p6 p3 p5 : Prop)
theorem file18_116398 : (((((p6 → p6) ∧ (p6 ∧ p5)) ∧ ((p2 → False) ∨ (True ∧ p7))) ∧ (((p5 → True) → (p1 → False)) ∨ ((p3 → False) → False))) → ((((p7 ∧ p5) ∨ (p7 ∧ p1)) → False) → (((p2 ∧ p7) ∨ (False → False)) → ((True ∧ False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p2 p4 p3 p1 : Prop)
theorem file18_116825 : (((((False → True) ∨ (p4 ∧ p4)) ∨ ((p3 ∨ p1) ∧ (p2 ∨ p3))) → False) → False) := by
  intro assump_1
  have assump_9 : (((False → True) ∨ (p4 ∧ p4)) ∨ ((p3 ∨ p1) ∧ (p2 ∨ p3))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p4 p0 p1 p6 p7 p2 p5 p3 : Prop)
theorem file18_117210 : (((((p3 ∧ p0) ∨ (p5 → False)) → False) ∨ (((p5 → True) → False) ∧ ((p4 ∧ p2) → False))) → ((((True ∧ p4) ∧ (p7 ∧ False)) → ((p3 ∨ p6) → (p7 ∧ p2))) ∨ (((p2 → False) ∧ (p1 → False)) → False))) := by
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    apply Or.inl
    intro assump_14
    intro assump_15
    apply And.intro
    cases assump_15
    case inl assump_16 =>
      cases assump_14
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          cases assump_21
          case intro assump_28 assump_29 =>
            apply False.elim assump_29
    case inr assump_17 =>
      cases assump_14
      case intro assump_36 assump_37 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          cases assump_37
          case intro assump_44 assump_45 =>
            apply False.elim assump_45
    cases assump_15
    case inl assump_50 =>
      cases assump_14
      case intro assump_54 assump_55 =>
        cases assump_54
        case intro assump_56 assump_57 =>
          cases assump_55
          case intro assump_62 assump_63 =>
            apply False.elim assump_63
    case inr assump_51 =>
      cases assump_14
      case intro assump_70 assump_71 =>
        cases assump_70
        case intro assump_72 assump_73 =>
          cases assump_71
          case intro assump_78 assump_79 =>
            apply False.elim assump_79
  case inr assump_11 =>
    cases assump_11
    case intro assump_84 assump_85 =>
      apply Or.inl
      intro assump_90
      intro assump_91
      apply And.intro
      cases assump_91
      case inl assump_92 =>
        cases assump_90
        case intro assump_96 assump_97 =>
          cases assump_96
          case intro assump_98 assump_99 =>
            cases assump_97
            case intro assump_104 assump_105 =>
              apply False.elim assump_105
      case inr assump_93 =>
        cases assump_90
        case intro assump_112 assump_113 =>
          cases assump_112
          case intro assump_114 assump_115 =>
            cases assump_113
            case intro assump_120 assump_121 =>
              apply False.elim assump_121
      cases assump_91
      case inl assump_126 =>
        cases assump_90
        case intro assump_130 assump_131 =>
          cases assump_130
          case intro assump_132 assump_133 =>
            cases assump_131
            case intro assump_138 assump_139 =>
              apply False.elim assump_139
      case inr assump_127 =>
        cases assump_90
        case intro assump_146 assump_147 =>
          cases assump_146
          case intro assump_148 assump_149 =>
            cases assump_147
            case intro assump_154 assump_155 =>
              apply False.elim assump_155


variable (p3 p4 p6 p5 p2 : Prop)
theorem file18_120051 : ((((((p2 ∧ p2) → (p5 ∨ True)) ∨ ((p4 → False) → False)) ∨ (((p6 ∨ p5) → (p2 → False)) ∨ ((p3 → False) ∨ (False → p6)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∧ p2) → (p5 ∨ True)) ∨ ((p4 → False) → False)) ∨ (((p6 ∨ p5) → (p2 → False)) ∨ ((p3 → False) ∨ (False → p6)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p3 p5 : Prop)
theorem file18_120621 : ((((((p5 ∧ p4) ∧ (False → False)) → ((False → True) ∧ (False → False))) → False) ∧ ((((True ∨ p3) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((True ∨ p3) → False) → False) := by
      intro assump_9
      have assump_20 : (True ∨ p3) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p4 p5 p0 p3 p2 p7 p1 : Prop)
theorem file18_121204 : (((((p1 ∧ p2) ∧ (p3 → False)) ∨ ((p1 → False) ∧ (False ∨ p2))) ∧ (((p5 ∧ p7) ∧ (p5 → False)) ∧ ((p4 → p0) ∧ (False ∧ p4)))) → ((((False ∨ p3) → (p0 ∧ p1)) → False) → False)) := by
  intro assump_6
  intro assump_7
  cases assump_6
  case intro assump_10 assump_11 =>
    cases assump_10
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_11
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              cases assump_26
              case intro assump_28 assump_29 =>
                cases assump_25
                case intro assump_36 assump_37 =>
                  cases assump_37
                  case intro assump_40 assump_41 =>
                    apply False.elim assump_40
    case inr assump_13 =>
      cases assump_13
      case intro assump_44 assump_45 =>
        cases assump_45
        case inl assump_48 =>
          apply False.elim assump_48
        case inr assump_49 =>
          cases assump_11
          case intro assump_54 assump_55 =>
            cases assump_54
            case intro assump_56 assump_57 =>
              cases assump_56
              case intro assump_58 assump_59 =>
                cases assump_55
                case intro assump_66 assump_67 =>
                  cases assump_67
                  case intro assump_70 assump_71 =>
                    apply False.elim assump_70


variable (p7 p2 p4 p5 : Prop)
theorem file18_122782 : (((((p5 ∨ True) ∧ (p5 → p5)) → False) → False) ∨ ((((p7 ∧ p4) ∧ (True → False)) ∧ ((p7 → False) → (p5 → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p5 ∨ True) ∧ (p5 → p5)) := by
    apply And.intro
    apply Or.inr
    apply True.intro
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p2 p1 p4 p6 : Prop)
theorem file18_123209 : ((((((False ∨ p6) ∧ (p1 → True)) ∧ ((p2 ∧ p6) ∨ (True → True))) → (((True → False) → (p3 → False)) ∨ ((p6 ∨ p2) ∨ (p4 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_51 : ((((False ∨ p6) ∧ (p1 → True)) ∧ ((p2 ∧ p6) ∨ (True → True))) → (((True → False) → (p3 → False)) ∨ ((p6 ∨ p2) ∨ (p4 ∨ p2)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          cases assump_7
          case inl assump_18 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply Or.inl
              intro assump_26
              intro assump_27
              have assump_52 : True := by
                apply True.intro
              let assump_32 := assump_26 assump_52
              apply False.elim assump_32
          case inr assump_19 =>
            apply Or.inl
            intro assump_38
            intro assump_39
            have assump_53 : True := by
              apply True.intro
            let assump_44 := assump_38 assump_53
            apply False.elim assump_44
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


