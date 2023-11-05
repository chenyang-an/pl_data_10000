variable (p6 p5 p0 p2 p7 p3 p1 p4 : Prop)
theorem file63_50 : (((((p7 ∨ p5) ∧ (p0 → False)) → False) ∧ (((p2 ∧ p4) ∨ (False → p5)) ∧ ((False ∧ p3) ∧ (False ∨ p1)))) → ((((True ∧ p4) ∧ (p5 ∨ False)) → ((True ∨ True) → (p1 → p5))) ∨ (((False ∨ p1) ∨ (False → p6)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
      case inr assump_9 =>
        cases assump_7
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            apply False.elim assump_26


variable (p7 p5 p3 p1 p2 p0 p4 : Prop)
theorem file63_951 : (((((p7 ∨ p3) ∨ (p1 ∧ p2)) → False) → (((p0 → p2) → False) → ((p3 ∧ p3) → False))) ∨ ((((p5 → False) ∨ (p7 → False)) ∧ ((p4 ∨ p7) → False)) ∨ (((p5 ∧ p4) ∨ (p7 ∧ False)) ∧ ((p2 ∧ True) → (p0 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_18 : ((p7 ∨ p3) ∨ (p1 ∧ p2)) := by
      apply Or.inl
      apply Or.inr
      exact assump_5
    let assump_14 := assump_1 assump_18
    apply False.elim assump_14


variable (p0 p6 p5 p1 p7 p3 p2 p4 : Prop)
theorem file63_1525 : (((((p7 → True) → (True → p2)) ∨ ((p5 ∨ p2) ∨ (p0 → False))) → (((p1 → p5) ∨ (p2 → p2)) → ((False → p5) ∨ (False → p3)))) → ((((p4 → False) ∧ (p1 ∨ p1)) → ((p7 ∧ p4) → False)) ∨ (((p7 → p3) → False) → ((p1 ∧ p2) ∨ (p6 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        have assump_32 : p4 := by
          exact assump_7
        let assump_21 := assump_12 assump_32
        apply False.elim assump_21
      case inr assump_17 =>
        have assump_33 : p4 := by
          exact assump_7
        let assump_28 := assump_12 assump_33
        apply False.elim assump_28


variable (p2 p3 p4 p6 p1 p5 p7 p0 : Prop)
theorem file63_2358 : (((((True → False) → (p6 → p6)) → False) → (((p6 ∨ p0) ∧ (p2 ∧ p3)) → ((p5 ∨ p7) → False))) ∨ ((((False ∧ p7) → (p4 → False)) ∨ ((p2 ∨ p1) → (p7 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          have assump_98 : ((True → False) → (p6 → p6)) := by
            intro assump_23
            intro assump_24
            exact assump_24
          let assump_22 := assump_1 assump_98
          apply False.elim assump_22
      case inr assump_11 =>
        cases assump_9
        case intro assump_34 assump_35 =>
          have assump_99 : ((True → False) → (p6 → p6)) := by
            intro assump_43
            intro assump_44
            exact assump_44
          let assump_42 := assump_1 assump_99
          apply False.elim assump_42
  case inr assump_5 =>
    cases assump_2
    case intro assump_54 assump_55 =>
      cases assump_54
      case inl assump_56 =>
        cases assump_55
        case intro assump_60 assump_61 =>
          have assump_100 : ((True → False) → (p6 → p6)) := by
            intro assump_69
            intro assump_70
            exact assump_70
          let assump_68 := assump_1 assump_100
          apply False.elim assump_68
      case inr assump_57 =>
        cases assump_55
        case intro assump_80 assump_81 =>
          have assump_101 : ((True → False) → (p6 → p6)) := by
            intro assump_89
            intro assump_90
            exact assump_90
          let assump_88 := assump_1 assump_101
          apply False.elim assump_88


variable (p7 p2 p3 p1 p5 p4 : Prop)
theorem file63_4168 : (((((p7 ∧ False) → (p5 → False)) → False) → False) ∨ ((((p1 → p7) ∨ (p1 ∨ p2)) ∧ ((p7 → False) → False)) ∧ (((p3 ∧ True) → False) ∧ ((p5 → False) ∨ (p2 ∧ p4))))) := by
  apply Or.inl
  intro assump_5
  have assump_22 : ((p7 ∧ False) → (p5 → False)) := by
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p1 p6 p4 p7 p0 p3 p2 p5 : Prop)
theorem file63_4683 : (((((p1 ∨ p7) → False) ∨ ((p6 ∧ True) ∧ (p3 → p2))) ∧ (((p4 → p4) → (p6 ∧ p1)) ∧ ((True → False) ∧ (p7 → p3)))) → ((((p6 → p2) ∨ (p7 ∧ p6)) ∨ ((p2 ∨ False) → (p2 → p6))) ∨ (((p6 → False) → (p7 ∨ p3)) → ((True → p5) ∧ (p3 ∨ p0))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_18
          have assump_56 : True := by
            apply True.intro
          let assump_23 := assump_12 assump_56
          apply False.elim assump_23
    case inr assump_5 =>
      cases assump_5
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_3
          case intro assump_37 assump_38 =>
            cases assump_38
            case intro assump_41 assump_42 =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              intro assump_47
              have assump_57 : True := by
                apply True.intro
              let assump_52 := assump_41 assump_57
              apply False.elim assump_52


variable (p3 p0 p4 p2 p1 p7 p5 : Prop)
theorem file63_6038 : (((((p3 → p3) → False) → False) ∨ (((p0 → False) → (p5 → p7)) → ((p4 → p4) ∧ (p1 ∧ False)))) ∨ ((((False ∨ p1) ∨ (p5 ∨ False)) → False) → (((p0 ∧ p7) ∨ (p3 → False)) ∨ ((p2 ∨ False) ∨ (False → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (p3 → p3) := by
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p4 p1 p6 p3 p7 p5 p2 : Prop)
theorem file63_6499 : ((((((p2 → p4) ∨ (p0 ∧ p3)) → False) → (((p2 → p6) ∧ (p0 ∧ True)) ∧ ((p0 ∨ p0) → (p0 → True)))) ∧ ((((p1 ∨ True) → (p7 → False)) ∨ ((p5 → False) ∨ (p6 → p2))) ∧ (((p1 → p7) ∧ (p5 → False)) ∧ ((p2 ∨ True) → False)))) → False) := by
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            have assump_63 : (p2 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_25 := assump_16 assump_63
            apply False.elim assump_25
      case inr assump_12 =>
        cases assump_12
        case inl assump_29 =>
          cases assump_10
          case intro assump_33 assump_34 =>
            cases assump_33
            case intro assump_35 assump_36 =>
              have assump_64 : (p2 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_43 := assump_34 assump_64
              apply False.elim assump_43
        case inr assump_30 =>
          cases assump_10
          case intro assump_49 assump_50 =>
            cases assump_49
            case intro assump_51 assump_52 =>
              have assump_65 : (p2 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_59 := assump_50 assump_65
              apply False.elim assump_59


variable (p7 p2 p5 p1 p6 p3 : Prop)
theorem file63_8098 : (((((p6 ∧ p3) → (p1 → False)) ∨ ((p1 ∧ p3) → False)) → (((p6 → False) → (False → False)) → False)) → ((((p2 ∧ p7) ∧ (p3 → False)) → ((p6 ∧ p5) → False)) ∨ (((p1 ∧ p3) ∨ (True ∧ p1)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_53 : (((p6 ∧ p3) → (p1 → False)) ∨ ((p1 ∧ p3) → False)) := by
          apply Or.inl
          intro assump_28
          intro assump_29
          cases assump_28
          case intro assump_32 assump_33 =>
            have assump_54 : p3 := by
              exact assump_33
            let assump_41 := assump_13 assump_54
            apply False.elim assump_41
        let assump_27 := assump_1 assump_53
        have assump_55 : ((p6 → False) → (False → False)) := by
          intro assump_46
          intro assump_47
          apply False.elim assump_47
        let assump_45 := assump_27 assump_55
        apply False.elim assump_45


variable (p4 p0 p5 p2 p6 p7 p3 p1 : Prop)
theorem file63_9259 : (((((p3 ∨ True) → (p1 → True)) → False) → (((True → p2) ∧ (True ∧ p2)) → ((p6 ∧ p3) → (p2 → False)))) ∨ ((((p7 ∨ p4) → False) ∨ ((p7 → False) → (p0 ∧ p7))) ∧ (((p5 ∨ p6) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_2
    case intro assump_13 assump_14 =>
      cases assump_14
      case intro assump_17 assump_18 =>
        have assump_31 : ((p3 ∨ True) → (p1 → True)) := by
          intro assump_26
          intro assump_27
          apply True.intro
        let assump_25 := assump_1 assump_31
        apply False.elim assump_25


variable (p3 p1 p0 p4 p2 p7 p6 p5 : Prop)
theorem file63_9991 : (((((True ∧ p4) → (p6 ∧ p1)) ∨ ((p3 → False) → (p3 ∧ p7))) → (((p4 → False) ∧ (p4 → False)) → ((False → True) ∨ (p5 ∧ p3)))) ∨ ((((False → False) → False) → ((p3 → p6) → (p1 ∨ p4))) ∨ (((p6 ∨ p0) ∧ (p6 → p2)) → False))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_5
    case inl assump_13 =>
      apply Or.inl
      intro assump_17
      apply True.intro
    case inr assump_14 =>
      apply Or.inl
      intro assump_20
      apply True.intro


variable (p3 p5 p6 : Prop)
theorem file63_10567 : (((((p3 → False) → (p6 ∧ p5)) → False) ∧ (((True ∧ p5) → (False ∨ p5)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((True ∧ p5) → (False ∨ p5)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inr
        exact assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p5 p4 p1 p0 p3 p2 p6 p7 : Prop)
theorem file63_11049 : (((((p5 → p6) → False) ∧ ((p0 → False) ∧ (p4 ∧ p6))) ∧ (((p1 ∨ False) → False) ∨ ((p0 ∧ p7) ∧ (p2 → False)))) → ((((p5 → p6) ∧ (True ∨ p3)) ∧ ((p6 → False) → (p1 → False))) ∧ (((p4 → p2) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_6
          case inl assump_21 =>
            exact assump_16
          case inr assump_22 =>
            cases assump_22
            case intro assump_25 assump_26 =>
              cases assump_25
              case intro assump_27 assump_28 =>
                exact assump_16
  cases assump_1
  case intro assump_35 assump_36 =>
    cases assump_35
    case intro assump_37 assump_38 =>
      cases assump_38
      case intro assump_41 assump_42 =>
        cases assump_42
        case intro assump_45 assump_46 =>
          cases assump_36
          case inl assump_51 =>
            apply Or.inl
            apply True.intro
          case inr assump_52 =>
            cases assump_52
            case intro assump_55 assump_56 =>
              cases assump_55
              case intro assump_57 assump_58 =>
                apply Or.inl
                apply True.intro
  intro assump_65
  intro assump_66
  cases assump_1
  case intro assump_71 assump_72 =>
    cases assump_71
    case intro assump_73 assump_74 =>
      cases assump_74
      case intro assump_77 assump_78 =>
        cases assump_78
        case intro assump_81 assump_82 =>
          cases assump_72
          case inl assump_87 =>
            have assump_167 : (p1 ∨ False) := by
              apply Or.inl
              exact assump_66
            let assump_91 := assump_87 assump_167
            apply False.elim assump_91
          case inr assump_88 =>
            cases assump_88
            case intro assump_95 assump_96 =>
              cases assump_95
              case intro assump_97 assump_98 =>
                have assump_168 : p0 := by
                  exact assump_97
                let assump_110 := assump_77 assump_168
                apply False.elim assump_110
  intro assump_114
  cases assump_1
  case intro assump_117 assump_118 =>
    cases assump_117
    case intro assump_119 assump_120 =>
      cases assump_120
      case intro assump_123 assump_124 =>
        cases assump_124
        case intro assump_127 assump_128 =>
          cases assump_118
          case inl assump_133 =>
            have assump_169 : (p5 → p6) := by
              intro assump_142
              exact assump_128
            let assump_141 := assump_119 assump_169
            apply False.elim assump_141
          case inr assump_134 =>
            cases assump_134
            case intro assump_148 assump_149 =>
              cases assump_148
              case intro assump_150 assump_151 =>
                have assump_170 : p0 := by
                  exact assump_150
                let assump_163 := assump_123 assump_170
                apply False.elim assump_163


variable (p5 p3 p4 p0 p7 : Prop)
theorem file63_14324 : (((((p0 → p7) ∧ (p3 ∧ p4)) → False) ∧ (((False ∨ p3) → False) ∧ ((False ∨ False) ∧ (p5 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          apply False.elim assump_13


variable (p6 p4 p1 p2 p5 p3 p0 : Prop)
theorem file63_14843 : ((((((p2 ∨ p6) ∨ (p5 ∧ p1)) ∧ ((p3 → p4) → False)) ∨ (((p6 ∨ False) ∧ (p0 → False)) ∨ ((False → False) ∧ (True ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p2 ∨ p6) ∨ (p5 ∧ p1)) ∧ ((p3 → p4) → False)) ∨ (((p6 ∨ False) ∧ (p0 → False)) ∨ ((False → False) ∧ (True ∨ p3)))) := by
    apply Or.inr
    apply Or.inr
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p1 p2 p6 p3 p5 p4 p7 : Prop)
theorem file63_15419 : (((((p5 ∨ p5) ∧ (p2 → False)) → ((p0 ∧ p6) → (p0 → p5))) ∨ (((p3 ∧ False) ∧ (p1 ∨ p6)) → False)) ∨ ((((p3 ∨ p3) ∧ (True ∧ p4)) → False) → (((p7 → p6) → (True ∨ p2)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        exact assump_14
      case inr assump_15 =>
        exact assump_15


variable (p6 p3 p5 p7 p0 p4 p1 p2 : Prop)
theorem file63_15982 : (((((p7 → p4) → (True → False)) ∧ ((p6 ∧ p5) ∨ (p4 → False))) → (((p0 ∨ True) → False) → ((p4 → False) ∨ (p0 → p3)))) ∨ ((((p4 → True) → False) → ((p0 ∧ p1) ∨ (p1 → False))) ∨ (((p5 ∨ p2) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inl
        intro assump_17
        have assump_41 : (p7 → p4) := by
          intro assump_24
          exact assump_17
        let assump_23 := assump_5 assump_41
        have assump_42 : True := by
          apply True.intro
        let assump_27 := assump_23 assump_42
        apply False.elim assump_27
    case inr assump_10 =>
      apply Or.inl
      intro assump_33
      have assump_43 : p4 := by
        exact assump_33
      let assump_37 := assump_10 assump_43
      apply False.elim assump_37


variable (p7 p4 p0 p3 p6 p5 p1 : Prop)
theorem file63_16988 : ((((((p4 → True) ∧ (p3 ∧ False)) ∧ ((p4 ∨ False) ∧ (p6 ∧ p1))) ∧ (((p3 → False) → (True → False)) → ((p4 ∨ p3) → False))) ∧ ((((False ∧ p6) → (p5 ∨ False)) ∨ ((p4 → False) ∨ (True → p0))) → (((p0 → p7) → False) ∨ ((False ∨ p4) → (True → p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p1 p7 p6 p0 p5 p4 p2 : Prop)
theorem file63_17664 : (((((p4 → True) ∨ (p7 ∧ p1)) ∨ ((p5 ∧ p6) ∧ (p0 → p7))) → False) → ((((False ∧ p6) → False) → ((p1 → p0) ∨ (True → p2))) → (((p5 → False) ∨ (True → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    have assump_28 : (((p4 → True) ∨ (p7 ∧ p1)) ∨ ((p5 ∧ p6) ∧ (p0 → p7))) := by
      apply Or.inl
      apply Or.inl
      intro assump_13
      apply True.intro
    let assump_12 := assump_1 assump_28
    apply False.elim assump_12
  case inr assump_5 =>
    have assump_29 : (((p4 → True) ∨ (p7 ∧ p1)) ∨ ((p5 ∧ p6) ∧ (p0 → p7))) := by
      apply Or.inl
      apply Or.inl
      intro assump_24
      apply True.intro
    let assump_23 := assump_1 assump_29
    apply False.elim assump_23


variable (p0 p3 p6 p1 p5 p7 p2 : Prop)
theorem file63_18484 : ((((((p5 ∧ p1) → False) ∧ ((p0 → p0) → False)) → (((p5 ∧ p2) ∧ (p5 → False)) ∧ ((p7 → p3) → (p6 → False)))) → ((((True → False) → False) ∨ ((p2 ∧ p6) ∧ (p6 → p7))) → False)) → False) := by
  intro assump_1
  have assump_78 : ((((p5 ∧ p1) → False) ∧ ((p0 → p0) → False)) → (((p5 ∧ p2) ∧ (p5 → False)) ∧ ((p7 → p3) → (p6 → False)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_79 : (p0 → p0) := by
        intro assump_13
        exact assump_13
      let assump_12 := assump_7 assump_79
      apply False.elim assump_12
    cases assump_5
    case intro assump_19 assump_20 =>
      have assump_80 : (p0 → p0) := by
        intro assump_26
        exact assump_26
      let assump_25 := assump_20 assump_80
      apply False.elim assump_25
    intro assump_32
    cases assump_5
    case intro assump_35 assump_36 =>
      have assump_81 : (p0 → p0) := by
        intro assump_42
        exact assump_42
      let assump_41 := assump_36 assump_81
      apply False.elim assump_41
    intro assump_48
    intro assump_49
    cases assump_5
    case intro assump_54 assump_55 =>
      have assump_82 : (p0 → p0) := by
        intro assump_61
        exact assump_61
      let assump_60 := assump_55 assump_82
      apply False.elim assump_60
  let assump_4 := assump_1 assump_78
  have assump_83 : (((True → False) → False) ∨ ((p2 ∧ p6) ∧ (p6 → p7))) := by
    apply Or.inl
    intro assump_68
    have assump_84 : True := by
      apply True.intro
    let assump_71 := assump_68 assump_84
    apply False.elim assump_71
  let assump_67 := assump_4 assump_83
  apply False.elim assump_67


variable (p5 p7 p3 p6 p1 p0 : Prop)
theorem file63_20243 : (((((p7 ∨ True) ∨ (p3 → p0)) ∨ ((p5 → False) → False)) → False) → ((((p3 ∨ p6) → False) ∧ ((p3 → p1) ∨ (False → p5))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      have assump_25 : (((p7 ∨ True) ∨ (p3 → p0)) ∨ ((p5 → False) → False)) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_13 := assump_1 assump_25
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_26 : (((p7 ∨ True) ∨ (p3 → p0)) ∨ ((p5 → False) → False)) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_21 := assump_1 assump_26
      apply False.elim assump_21


variable (p5 p2 p1 p7 p0 p3 : Prop)
theorem file63_21081 : ((((((p5 → False) → False) → False) → False) ∧ ((((p1 ∨ p3) ∨ (p1 ∧ True)) ∨ ((False → p0) ∨ (p7 → False))) → (((p2 ∨ p5) ∨ (p2 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (((p1 ∨ p3) ∨ (p1 ∧ True)) ∨ ((False → p0) ∨ (p7 → False))) := by
      apply Or.inr
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_28
    have assump_29 : ((p2 ∨ p5) ∨ (p2 → False)) := by
      apply Or.inr
      intro assump_13
      have assump_30 : (((p1 ∨ p3) ∨ (p1 ∧ True)) ∨ ((False → p0) ∨ (p7 → False))) := by
        apply Or.inr
        apply Or.inl
        intro assump_18
        apply False.elim assump_18
      let assump_17 := assump_3 assump_30
      have assump_31 : ((p2 ∨ p5) ∨ (p2 → False)) := by
        apply Or.inl
        apply Or.inl
        exact assump_13
      let assump_21 := assump_17 assump_31
      apply False.elim assump_21
    let assump_12 := assump_8 assump_29
    apply False.elim assump_12


variable (p3 p1 p2 p7 p5 p6 : Prop)
theorem file63_22186 : (((((False ∧ False) ∧ (True ∨ False)) → False) ∨ (((True → False) ∨ (p3 → p3)) ∧ ((p2 → False) → (p3 ∨ p7)))) ∨ ((((True ∧ True) ∧ (False → False)) ∨ ((True → False) ∨ (p2 → False))) ∧ (((False → False) ∧ (p5 → False)) ∨ ((p6 → False) ∨ (p1 ∧ p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply False.elim assump_8


variable (p3 p7 p4 p2 p1 p5 : Prop)
theorem file63_22688 : ((((((p3 → False) → False) ∨ ((p5 → p3) → (p5 ∨ False))) ∨ (((p3 ∧ p1) ∧ (p7 ∧ p4)) → False)) ∧ ((((p1 ∧ False) → (p4 ∨ p2)) ∨ ((p3 ∨ p4) → (p3 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_53 : (((p1 ∧ False) → (p4 ∨ p2)) ∨ ((p3 ∨ p4) → (p3 → p7))) := by
          apply Or.inl
          intro assump_13
          cases assump_13
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
        let assump_12 := assump_3 assump_53
        apply False.elim assump_12
      case inr assump_7 =>
        have assump_54 : (((p1 ∧ False) → (p4 ∨ p2)) ∨ ((p3 ∨ p4) → (p3 → p7))) := by
          apply Or.inl
          intro assump_28
          cases assump_28
          case intro assump_29 assump_30 =>
            apply False.elim assump_30
        let assump_27 := assump_3 assump_54
        apply False.elim assump_27
    case inr assump_5 =>
      have assump_55 : (((p1 ∧ False) → (p4 ∨ p2)) ∨ ((p3 ∨ p4) → (p3 → p7))) := by
        apply Or.inl
        intro assump_43
        cases assump_43
        case intro assump_44 assump_45 =>
          apply False.elim assump_45
      let assump_42 := assump_3 assump_55
      apply False.elim assump_42


variable (p7 p5 p0 p3 p4 p1 p6 : Prop)
theorem file63_24093 : (((((True ∧ p4) ∨ (p3 ∨ p7)) ∧ ((p3 → False) → (p6 → p1))) → False) → ((((p5 ∧ True) → False) ∨ ((p1 → p0) ∧ (True ∨ p4))) → (((False ∨ False) ∧ (False → False)) → ((True → p1) ∧ (False ∨ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      apply False.elim assump_9
    case inr assump_10 =>
      apply False.elim assump_10
  cases assump_3
  case intro assump_15 assump_16 =>
    cases assump_15
    case inl assump_17 =>
      apply False.elim assump_17
    case inr assump_18 =>
      apply False.elim assump_18


variable (p2 p7 p1 : Prop)
theorem file63_24809 : ((((((p2 ∨ p1) → False) ∧ ((True → False) ∧ (p7 → p2))) → False) → False) → False) := by
  intro assump_10
  have assump_33 : ((((p2 ∨ p1) → False) ∧ ((True → False) ∧ (p7 → p2))) → False) := by
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_16
      case intro assump_19 assump_20 =>
        have assump_34 : True := by
          apply True.intro
        let assump_26 := assump_19 assump_34
        apply False.elim assump_26
  let assump_13 := assump_10 assump_33
  apply False.elim assump_13


variable (p3 p1 : Prop)
theorem file63_25403 : ((((((p3 → False) → (p3 → True)) ∧ ((False ∨ True) ∧ (False ∧ p3))) → (((p1 ∧ p1) → False) → False)) → False) → False) := by
  intro assump_10
  have assump_37 : ((((p3 → False) → (p3 → True)) ∧ ((False ∨ True) ∧ (False ∧ p3))) → (((p1 ∧ p1) → False) → False)) := by
    intro assump_14
    intro assump_15
    cases assump_14
    case intro assump_18 assump_19 =>
      cases assump_19
      case intro assump_22 assump_23 =>
        cases assump_22
        case inl assump_24 =>
          apply False.elim assump_24
        case inr assump_25 =>
          cases assump_23
          case intro assump_30 assump_31 =>
            apply False.elim assump_30
  let assump_13 := assump_10 assump_37
  apply False.elim assump_13


variable (p0 p7 p3 p6 p2 : Prop)
theorem file63_26185 : ((((((p3 ∨ p7) → (False → False)) → False) → (((p0 ∧ p2) ∨ (p3 ∧ p6)) → ((p3 ∧ p7) ∧ (p6 → p6)))) → False) → False) := by
  intro assump_28
  have assump_118 : ((((p3 ∨ p7) → (False → False)) → False) → (((p0 ∧ p2) ∨ (p3 ∧ p6)) → ((p3 ∧ p7) ∧ (p6 → p6)))) := by
    intro assump_32
    intro assump_33
    apply And.intro
    apply And.intro
    cases assump_33
    case inl assump_34 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        have assump_119 : ((p3 ∨ p7) → (False → False)) := by
          intro assump_45
          intro assump_46
          apply False.elim assump_46
        let assump_44 := assump_32 assump_119
        apply False.elim assump_44
    case inr assump_35 =>
      cases assump_35
      case intro assump_52 assump_53 =>
        exact assump_52
    cases assump_33
    case inl assump_60 =>
      cases assump_60
      case intro assump_62 assump_63 =>
        have assump_120 : ((p3 ∨ p7) → (False → False)) := by
          intro assump_71
          intro assump_72
          apply False.elim assump_72
        let assump_70 := assump_32 assump_120
        apply False.elim assump_70
    case inr assump_61 =>
      cases assump_61
      case intro assump_78 assump_79 =>
        have assump_121 : ((p3 ∨ p7) → (False → False)) := by
          intro assump_87
          intro assump_88
          apply False.elim assump_88
        let assump_86 := assump_32 assump_121
        apply False.elim assump_86
    intro assump_94
    cases assump_33
    case inl assump_97 =>
      cases assump_97
      case intro assump_99 assump_100 =>
        exact assump_94
    case inr assump_98 =>
      cases assump_98
      case intro assump_107 assump_108 =>
        exact assump_108
  let assump_31 := assump_28 assump_118
  apply False.elim assump_31


variable (p1 p7 p4 p2 p0 p6 : Prop)
theorem file63_28036 : (((((p2 ∨ p7) → (p2 ∨ True)) ∧ ((p1 → False) ∧ (False ∧ p7))) ∨ (((p0 ∧ False) ∧ (p1 ∧ p0)) ∧ ((True → p6) → False))) → ((((p4 → False) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
  case inr assump_6 =>
    cases assump_6
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          apply False.elim assump_24


variable (p4 p6 p1 p7 p5 p3 p2 : Prop)
theorem file63_28807 : (((((False → p6) ∧ (p3 ∧ p7)) → False) ∧ (((p2 ∨ p1) ∧ (p4 ∨ True)) → False)) → ((((p2 ∧ p3) → False) → False) → (((p6 ∧ p1) ∧ (p7 → p1)) ∧ ((True → p5) ∧ (p5 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_162 : ((p2 ∧ p3) → False) := by
      intro assump_17
      cases assump_17
      case intro assump_18 assump_19 =>
        have assump_163 : ((p2 ∨ p1) ∧ (p4 ∨ True)) := by
          apply And.intro
          apply Or.inl
          exact assump_18
          apply Or.inr
          apply True.intro
        let assump_26 := assump_6 assump_163
        apply False.elim assump_26
    let assump_16 := assump_2 assump_162
    apply False.elim assump_16
  cases assump_1
  case intro assump_35 assump_36 =>
    have assump_164 : ((p2 ∧ p3) → False) := by
      intro assump_47
      cases assump_47
      case intro assump_48 assump_49 =>
        have assump_165 : ((p2 ∨ p1) ∧ (p4 ∨ True)) := by
          apply And.intro
          apply Or.inl
          exact assump_48
          apply Or.inr
          apply True.intro
        let assump_56 := assump_36 assump_165
        apply False.elim assump_56
    let assump_46 := assump_2 assump_164
    apply False.elim assump_46
  intro assump_63
  cases assump_1
  case intro assump_68 assump_69 =>
    have assump_166 : ((p2 ∧ p3) → False) := by
      intro assump_80
      cases assump_80
      case intro assump_81 assump_82 =>
        have assump_167 : ((p2 ∨ p1) ∧ (p4 ∨ True)) := by
          apply And.intro
          apply Or.inl
          exact assump_81
          apply Or.inr
          apply True.intro
        let assump_89 := assump_69 assump_167
        apply False.elim assump_89
    let assump_79 := assump_2 assump_166
    apply False.elim assump_79
  apply And.intro
  intro assump_96
  cases assump_1
  case intro assump_101 assump_102 =>
    have assump_168 : ((p2 ∧ p3) → False) := by
      intro assump_113
      cases assump_113
      case intro assump_114 assump_115 =>
        have assump_169 : ((p2 ∨ p1) ∧ (p4 ∨ True)) := by
          apply And.intro
          apply Or.inl
          exact assump_114
          apply Or.inr
          apply True.intro
        let assump_122 := assump_102 assump_169
        apply False.elim assump_122
    let assump_112 := assump_2 assump_168
    apply False.elim assump_112
  intro assump_129
  cases assump_1
  case intro assump_134 assump_135 =>
    have assump_170 : ((p2 ∧ p3) → False) := by
      intro assump_146
      cases assump_146
      case intro assump_147 assump_148 =>
        have assump_171 : ((p2 ∨ p1) ∧ (p4 ∨ True)) := by
          apply And.intro
          apply Or.inl
          exact assump_147
          apply Or.inr
          apply True.intro
        let assump_155 := assump_135 assump_171
        apply False.elim assump_155
    let assump_145 := assump_2 assump_170
    apply False.elim assump_145


variable (p1 p7 p2 p4 p5 p6 p3 : Prop)
theorem file63_31835 : ((((((p5 ∨ p1) → (False → False)) ∨ ((p6 → p3) → (p3 ∨ p2))) ∨ (((p7 ∨ p4) ∨ (p4 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p5 ∨ p1) → (False → False)) ∨ ((p6 → p3) → (p3 ∨ p2))) ∨ (((p7 ∨ p4) ∨ (p4 → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p6 p0 p5 p1 p3 p2 p7 p4 : Prop)
theorem file63_32334 : (((((p6 → p1) → (False → p2)) ∨ ((p3 → False) ∧ (True ∨ p4))) → (((p7 → p6) → False) → ((p4 → p1) → (p3 → p3)))) ∨ ((((p3 → False) ∧ (p5 ∧ p1)) → False) ∧ (((p1 → p6) → (p6 → False)) → ((p0 ∨ p6) ∧ (p4 ∧ p2))))) := by
  apply Or.inl
  intro assump_20
  intro assump_21
  intro assump_22
  intro assump_23
  cases assump_20
  case inl assump_30 =>
    exact assump_23
  case inr assump_31 =>
    cases assump_31
    case intro assump_34 assump_35 =>
      cases assump_35
      case inl assump_38 =>
        exact assump_23
      case inr assump_39 =>
        exact assump_23


variable (p3 p2 p6 p1 p5 p0 p4 : Prop)
theorem file63_32972 : (((((False → p6) ∧ (p3 → False)) → False) ∨ (((p1 ∨ p4) ∨ (p0 → p2)) → ((p6 ∧ p1) → (p0 → p0)))) → ((((True ∨ p2) ∨ (p6 → p5)) ∨ ((False → p0) → (p6 ∧ p4))) ∨ (((p1 → p4) → (p1 ∨ p4)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro


variable (p6 p5 p3 p2 p0 p4 : Prop)
theorem file63_33491 : ((((((p4 ∧ p6) → (p5 ∧ p0)) → ((False ∨ p2) → False)) → False) ∧ ((((p4 → p3) → False) → ((False → False) ∨ (True → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p4 → p3) → False) → ((False → False) ∨ (True → p3))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p1 p4 p7 p0 p6 p2 p5 : Prop)
theorem file63_34016 : ((((((p0 → False) ∧ (p6 → p4)) ∧ ((False → False) → False)) → (((p6 → False) → False) → False)) ∧ ((((p6 ∧ False) → (True → False)) → False) ∨ (((p5 ∧ False) ∧ (True → p7)) ∧ ((False → p4) ∧ (p1 ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_34 : ((p6 ∧ False) → (True → False)) := by
        intro assump_11
        intro assump_12
        cases assump_11
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
      let assump_10 := assump_6 assump_34
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_29


variable (p4 p2 p3 p1 p5 : Prop)
theorem file63_34953 : ((((((p2 ∧ False) → (p4 → False)) → False) → (((p1 → False) ∧ (p5 ∧ p4)) ∨ ((False → p3) → False))) → False) → False) := by
  intro assump_1
  have assump_47 : ((((p2 ∧ False) → (p4 → False)) → False) → (((p1 → False) ∧ (p5 ∧ p4)) ∨ ((False → p3) → False))) := by
    intro assump_5
    apply Or.inr
    intro assump_26
    have assump_48 : ((p2 ∧ False) → (p4 → False)) := by
      intro assump_31
      intro assump_32
      cases assump_31
      case intro assump_35 assump_36 =>
        apply False.elim assump_36
    let assump_30 := assump_5 assump_48
    apply False.elim assump_30
  let assump_4 := assump_1 assump_47
  apply False.elim assump_4


variable (p4 p0 p5 p6 p1 p3 p7 p2 : Prop)
theorem file63_35673 : (((((p7 ∧ p6) ∧ (p4 → False)) ∨ ((p0 → False) ∨ (True → False))) → (((False → p3) ∧ (p5 → p1)) → ((False → p6) ∨ (p7 → p4)))) ∨ ((((p4 ∧ True) ∨ (p0 ∧ p2)) ∨ ((True ∧ p1) ∨ (p1 ∨ p0))) → (((p0 → p7) ∧ (p6 → p0)) ∧ ((p1 → False) ∨ (p6 ∨ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
    case inr assump_10 =>
      cases assump_10
      case inl assump_24 =>
        apply Or.inl
        intro assump_28
        apply False.elim assump_28
      case inr assump_25 =>
        apply Or.inl
        intro assump_33
        apply False.elim assump_33


variable (p5 p6 p0 p1 p3 p4 p2 : Prop)
theorem file63_36609 : ((((((p4 → p6) ∧ (p5 ∨ True)) → False) ∨ (((False → False) → False) ∧ ((p5 ∧ True) ∧ (p4 ∧ p5)))) ∧ ((((p5 ∧ False) → False) → False) ∧ (((p3 → p0) ∧ (True → p2)) ∨ ((False ∧ p1) → (p4 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_106 : ((p5 ∧ False) → False) := by
              intro assump_24
              cases assump_24
              case intro assump_25 assump_26 =>
                apply False.elim assump_26
            let assump_23 := assump_8 assump_106
            apply False.elim assump_23
        case inr assump_13 =>
          have assump_107 : ((p5 ∧ False) → False) := by
            intro assump_38
            cases assump_38
            case intro assump_39 assump_40 =>
              apply False.elim assump_40
          let assump_37 := assump_8 assump_107
          apply False.elim assump_37
    case inr assump_5 =>
      cases assump_5
      case intro assump_48 assump_49 =>
        cases assump_49
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_53
            case intro assump_60 assump_61 =>
              cases assump_3
              case intro assump_66 assump_67 =>
                cases assump_67
                case inl assump_70 =>
                  cases assump_70
                  case intro assump_72 assump_73 =>
                    have assump_108 : ((p5 ∧ False) → False) := by
                      intro assump_82
                      cases assump_82
                      case intro assump_83 assump_84 =>
                        apply False.elim assump_84
                    let assump_81 := assump_66 assump_108
                    apply False.elim assump_81
                case inr assump_71 =>
                  have assump_109 : ((p5 ∧ False) → False) := by
                    intro assump_96
                    cases assump_96
                    case intro assump_97 assump_98 =>
                      apply False.elim assump_98
                  let assump_95 := assump_66 assump_109
                  apply False.elim assump_95


variable (p1 p7 p4 p2 p6 p0 p5 : Prop)
theorem file63_39054 : (((((p7 → False) ∨ (p7 ∨ p0)) → ((p6 ∨ p2) ∨ (p4 ∧ False))) ∨ (((p0 ∨ p5) ∨ (p4 ∨ True)) → False)) → ((((p6 ∨ True) ∧ (p1 ∧ p5)) → ((p4 ∧ p0) ∨ (p2 → p2))) ∨ (((p6 → False) → False) ∧ ((p2 → p6) ∧ (p6 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          apply Or.inr
          intro assump_19
          exact assump_19
      case inr assump_10 =>
        cases assump_8
        case intro assump_24 assump_25 =>
          apply Or.inr
          intro assump_30
          exact assump_30
  case inr assump_3 =>
    apply Or.inl
    intro assump_35
    cases assump_35
    case intro assump_36 assump_37 =>
      cases assump_36
      case inl assump_38 =>
        cases assump_37
        case intro assump_42 assump_43 =>
          apply Or.inr
          intro assump_48
          exact assump_48
      case inr assump_39 =>
        cases assump_37
        case intro assump_53 assump_54 =>
          apply Or.inr
          intro assump_59
          exact assump_59


variable (p3 p5 p0 p6 p2 p1 p7 p4 : Prop)
theorem file63_40322 : (((((p6 ∧ p7) ∨ (p5 ∨ p0)) ∧ ((p3 → False) ∧ (p1 ∨ False))) ∧ (((p4 → False) ∧ (True → False)) ∧ ((p2 → p0) ∨ (p5 ∧ True)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_15
            case inl assump_18 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_23
                  case inl assump_30 =>
                    have assump_134 : True := by
                      apply True.intro
                    let assump_35 := assump_25 assump_134
                    apply False.elim assump_35
                  case inr assump_31 =>
                    cases assump_31
                    case intro assump_39 assump_40 =>
                      have assump_135 : True := by
                        apply True.intro
                      let assump_46 := assump_25 assump_135
                      apply False.elim assump_46
            case inr assump_19 =>
              apply False.elim assump_19
      case inr assump_7 =>
        cases assump_7
        case inl assump_52 =>
          cases assump_5
          case intro assump_56 assump_57 =>
            cases assump_57
            case inl assump_60 =>
              cases assump_3
              case intro assump_64 assump_65 =>
                cases assump_64
                case intro assump_66 assump_67 =>
                  cases assump_65
                  case inl assump_72 =>
                    have assump_136 : True := by
                      apply True.intro
                    let assump_77 := assump_67 assump_136
                    apply False.elim assump_77
                  case inr assump_73 =>
                    cases assump_73
                    case intro assump_81 assump_82 =>
                      have assump_137 : True := by
                        apply True.intro
                      let assump_88 := assump_67 assump_137
                      apply False.elim assump_88
            case inr assump_61 =>
              apply False.elim assump_61
        case inr assump_53 =>
          cases assump_5
          case intro assump_96 assump_97 =>
            cases assump_97
            case inl assump_100 =>
              cases assump_3
              case intro assump_104 assump_105 =>
                cases assump_104
                case intro assump_106 assump_107 =>
                  cases assump_105
                  case inl assump_112 =>
                    have assump_138 : True := by
                      apply True.intro
                    let assump_117 := assump_107 assump_138
                    apply False.elim assump_117
                  case inr assump_113 =>
                    cases assump_113
                    case intro assump_121 assump_122 =>
                      have assump_139 : True := by
                        apply True.intro
                      let assump_128 := assump_107 assump_139
                      apply False.elim assump_128
            case inr assump_101 =>
              apply False.elim assump_101


variable (p6 p7 p5 : Prop)
theorem file63_43766 : (((((False ∧ p7) → (p5 → p7)) ∨ ((p6 ∨ p5) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((False ∧ p7) → (p5 → p7)) ∨ ((p6 ∨ p5) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p7 p0 p2 p4 p6 p5 p1 : Prop)
theorem file63_44210 : (((((False ∧ p4) → False) ∧ ((p5 → False) ∧ (p1 → p4))) → (((True → False) → False) ∨ ((p0 → False) ∨ (p6 → False)))) ∨ ((((p3 → p7) → False) → ((p0 → p3) → (p7 → False))) ∧ (((p2 ∨ p3) ∧ (p5 → p3)) ∨ ((p5 ∧ p7) ∧ (False → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      have assump_19 : True := by
        apply True.intro
      let assump_15 := assump_12 assump_19
      apply False.elim assump_15


variable (p6 p7 p5 p3 : Prop)
theorem file63_44818 : ((((((False → False) ∧ (False ∧ p7)) → False) ∧ (((p6 → p6) ∨ (p5 → False)) ∨ ((False → False) ∧ (p3 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False → False) ∧ (False ∧ p7)) → False) ∧ (((p6 → p6) ∨ (p5 → False)) ∨ ((False → False) ∧ (p3 ∧ p6)))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    apply Or.inl
    apply Or.inl
    intro assump_14
    exact assump_14
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p7 p0 p3 p5 p2 : Prop)
theorem file63_45488 : (((((True ∧ p5) ∨ (True → p2)) ∨ ((p7 ∨ True) ∧ (p2 → False))) ∧ (((p3 → False) ∨ (p0 → False)) ∧ ((p3 ∨ p7) ∧ (True → False)))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_9
          case intro assump_20 assump_21 =>
            cases assump_20
            case inl assump_22 =>
              cases assump_21
              case intro assump_26 assump_27 =>
                cases assump_26
                case inl assump_28 =>
                  have assump_226 : True := by
                    apply True.intro
                  let assump_34 := assump_27 assump_226
                  apply False.elim assump_34
                case inr assump_29 =>
                  have assump_227 : True := by
                    apply True.intro
                  let assump_42 := assump_27 assump_227
                  apply False.elim assump_42
            case inr assump_23 =>
              cases assump_21
              case intro assump_48 assump_49 =>
                cases assump_48
                case inl assump_50 =>
                  have assump_228 : True := by
                    apply True.intro
                  let assump_56 := assump_49 assump_228
                  apply False.elim assump_56
                case inr assump_51 =>
                  have assump_229 : True := by
                    apply True.intro
                  let assump_64 := assump_49 assump_229
                  apply False.elim assump_64
      case inr assump_13 =>
        cases assump_9
        case intro assump_70 assump_71 =>
          cases assump_70
          case inl assump_72 =>
            cases assump_71
            case intro assump_76 assump_77 =>
              cases assump_76
              case inl assump_78 =>
                have assump_230 : True := by
                  apply True.intro
                let assump_84 := assump_77 assump_230
                apply False.elim assump_84
              case inr assump_79 =>
                have assump_231 : True := by
                  apply True.intro
                let assump_92 := assump_77 assump_231
                apply False.elim assump_92
          case inr assump_73 =>
            cases assump_71
            case intro assump_98 assump_99 =>
              cases assump_98
              case inl assump_100 =>
                have assump_232 : True := by
                  apply True.intro
                let assump_106 := assump_99 assump_232
                apply False.elim assump_106
              case inr assump_101 =>
                have assump_233 : True := by
                  apply True.intro
                let assump_114 := assump_99 assump_233
                apply False.elim assump_114
    case inr assump_11 =>
      cases assump_11
      case intro assump_118 assump_119 =>
        cases assump_118
        case inl assump_120 =>
          cases assump_9
          case intro assump_126 assump_127 =>
            cases assump_126
            case inl assump_128 =>
              cases assump_127
              case intro assump_132 assump_133 =>
                cases assump_132
                case inl assump_134 =>
                  have assump_234 : True := by
                    apply True.intro
                  let assump_140 := assump_133 assump_234
                  apply False.elim assump_140
                case inr assump_135 =>
                  have assump_235 : True := by
                    apply True.intro
                  let assump_148 := assump_133 assump_235
                  apply False.elim assump_148
            case inr assump_129 =>
              cases assump_127
              case intro assump_154 assump_155 =>
                cases assump_154
                case inl assump_156 =>
                  have assump_236 : True := by
                    apply True.intro
                  let assump_162 := assump_155 assump_236
                  apply False.elim assump_162
                case inr assump_157 =>
                  have assump_237 : True := by
                    apply True.intro
                  let assump_170 := assump_155 assump_237
                  apply False.elim assump_170
        case inr assump_121 =>
          cases assump_9
          case intro assump_178 assump_179 =>
            cases assump_178
            case inl assump_180 =>
              cases assump_179
              case intro assump_184 assump_185 =>
                cases assump_184
                case inl assump_186 =>
                  have assump_238 : True := by
                    apply True.intro
                  let assump_192 := assump_185 assump_238
                  apply False.elim assump_192
                case inr assump_187 =>
                  have assump_239 : True := by
                    apply True.intro
                  let assump_200 := assump_185 assump_239
                  apply False.elim assump_200
            case inr assump_181 =>
              cases assump_179
              case intro assump_206 assump_207 =>
                cases assump_206
                case inl assump_208 =>
                  have assump_240 : True := by
                    apply True.intro
                  let assump_214 := assump_207 assump_240
                  apply False.elim assump_214
                case inr assump_209 =>
                  have assump_241 : True := by
                    apply True.intro
                  let assump_222 := assump_207 assump_241
                  apply False.elim assump_222


variable (p2 p0 p6 p1 p5 p7 : Prop)
theorem file63_51236 : (((((p7 → p7) → (False ∧ p2)) → False) ∧ (((p7 → p7) → False) → ((p6 → False) → False))) ∨ ((((p5 → p1) ∨ (p0 ∧ p2)) ∧ ((p7 ∨ False) ∧ (p5 ∨ p5))) → (((False → False) → False) ∧ ((True → p6) → False)))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_25 : (p7 → p7) := by
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_25
  let assump_8 := And.left assump_4
  apply False.elim assump_8
  intro assump_12
  intro assump_13
  have assump_26 : (p7 → p7) := by
    intro assump_19
    exact assump_19
  let assump_18 := assump_12 assump_26
  apply False.elim assump_18


variable (p7 p1 p5 p4 p3 p6 : Prop)
theorem file63_51908 : ((((((p7 → False) ∧ (p1 → False)) ∧ ((False → p4) → (True → False))) → (((p6 → False) → (p6 → p5)) ∧ ((p6 → p5) ∨ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_55 : ((((p7 → False) ∧ (p1 → False)) ∧ ((False → p4) → (True → False))) → (((p6 → False) → (p6 → p5)) ∧ ((p6 → p5) ∨ (p3 → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_56 : (False → p4) := by
          intro assump_23
          apply False.elim assump_23
        let assump_22 := assump_13 assump_56
        have assump_57 : True := by
          apply True.intro
        let assump_26 := assump_22 assump_57
        apply False.elim assump_26
    cases assump_5
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        apply Or.inl
        intro assump_40
        have assump_58 : (False → p4) := by
          intro assump_45
          apply False.elim assump_45
        let assump_44 := assump_31 assump_58
        have assump_59 : True := by
          apply True.intro
        let assump_48 := assump_44 assump_59
        apply False.elim assump_48
  let assump_4 := assump_1 assump_55
  apply False.elim assump_4


variable (p2 p6 p5 p1 : Prop)
theorem file63_53301 : ((((((p5 → True) ∨ (p1 ∨ False)) → False) → (((p2 ∨ p2) ∨ (True ∨ p1)) ∨ ((False ∨ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 → True) ∨ (p1 ∨ False)) → False) → (((p2 ∨ p2) ∨ (True ∨ p1)) ∨ ((False ∨ p6) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p1 p2 p5 p7 p3 p6 : Prop)
theorem file63_53780 : (((((p5 ∨ p0) → False) ∧ ((p3 → False) ∧ (p3 → p7))) → (((False → p0) ∨ (p6 ∨ True)) ∨ ((p6 ∨ p1) → False))) ∨ ((((p1 → False) → False) ∨ ((p1 ∧ True) → (p1 → False))) ∧ (((p1 → p0) → False) ∧ ((p2 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      apply False.elim assump_12


variable (p5 p1 p3 p7 p0 : Prop)
theorem file63_54293 : (((((p0 → False) → False) ∧ ((True ∧ p3) ∧ (False ∨ False))) → False) ∨ ((((p1 → False) ∨ (p7 → p1)) ∨ ((p5 ∨ p3) → (p0 ∨ p7))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          apply False.elim assump_15


variable (p4 p2 p5 p3 p1 p6 : Prop)
theorem file63_54851 : ((((((False ∧ p1) ∨ (p2 ∧ p6)) ∧ ((p4 → False) ∨ (p2 ∧ p3))) → (((p1 ∧ False) ∧ (True ∧ p5)) → False)) ∧ ((((p5 ∨ False) ∧ (p4 ∧ False)) → ((p5 → p4) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_30 : (((p5 ∨ False) ∧ (p4 ∧ False)) → ((p5 → p4) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_14
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
        case inr assump_16 =>
          apply False.elim assump_16
    let assump_8 := assump_3 assump_30
    apply False.elim assump_8


variable (p1 p2 p3 p0 p6 p5 p7 p4 : Prop)
theorem file63_55654 : (((((p0 → p3) ∧ (p1 ∨ True)) → ((p2 ∧ p6) → (True → p6))) → (((p6 ∧ p0) → (True → p3)) → ((False ∧ True) → False))) ∨ ((((p4 → False) ∧ (p5 ∧ p7)) → ((False ∨ p7) → False)) ∨ (((p0 ∧ p0) → False) → ((p2 → False) → (p4 ∧ p0))))) := by
  apply Or.inl
  intro assump_20
  intro assump_21
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    apply False.elim assump_23


variable (p5 p1 p2 p4 p6 p7 : Prop)
theorem file63_56102 : (((((True → False) → (p4 ∧ p2)) → ((False ∧ False) ∧ (p6 ∨ p6))) → (((p1 → p6) ∨ (p1 ∧ p5)) ∨ ((p1 → False) → (p1 → False)))) ∨ ((((p7 → False) → False) → False) ∧ (((p1 → False) → False) ∨ ((p7 ∨ p2) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_27 : ((True → False) → (p4 ∧ p2)) := by
    intro assump_9
    apply And.intro
    have assump_28 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_28
    apply False.elim assump_12
    have assump_29 : True := by
      apply True.intro
    let assump_18 := assump_9 assump_29
    apply False.elim assump_18
  let assump_8 := assump_1 assump_27
  let assump_22 := And.left assump_8
  let assump_23 := And.left assump_22
  apply False.elim assump_23


variable (p4 p5 p3 p0 p7 p1 p6 : Prop)
theorem file63_56949 : (((((p3 ∧ p1) → (p7 → True)) → False) → (((p1 → False) ∨ (p4 → False)) → False)) ∨ ((((p6 ∨ False) → (True ∨ p7)) ∨ ((True ∧ True) → False)) ∧ (((p0 → p5) ∧ (False → False)) ∨ ((p6 ∧ p6) ∨ (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_25 : ((p3 ∧ p1) → (p7 → True)) := by
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_9 := assump_1 assump_25
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_26 : ((p3 ∧ p1) → (p7 → True)) := by
      intro assump_20
      intro assump_21
      apply True.intro
    let assump_19 := assump_1 assump_26
    apply False.elim assump_19


variable (p4 p7 p6 p1 p0 : Prop)
theorem file63_57710 : ((((((p7 → p6) ∧ (p7 → p1)) ∨ ((p7 → p4) → False)) → False) ∧ ((((p0 ∨ True) → (p1 ∨ False)) → ((p1 ∧ False) → (p1 ∧ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_26 : (((p0 ∨ True) → (p1 ∨ False)) → ((p1 ∧ False) → (p1 ∧ p6))) := by
      intro assump_9
      intro assump_10
      apply And.intro
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
      cases assump_10
      case intro assump_17 assump_18 =>
        apply False.elim assump_18
    let assump_8 := assump_3 assump_26
    apply False.elim assump_8


variable (p0 p6 p4 p5 p1 : Prop)
theorem file63_58398 : (((((p4 ∨ p4) → False) → False) ∧ (((p5 ∧ p4) ∨ (p1 → False)) ∧ ((p6 ∧ False) ∧ (p4 → False)))) → ((((p1 → False) → (p0 ∨ True)) ∨ ((p1 → p6) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_12
            case intro assump_21 assump_22 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                apply False.elim assump_24
        case inr assump_14 =>
          cases assump_12
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              apply False.elim assump_34
  case inr assump_4 =>
    cases assump_1
    case intro assump_41 assump_42 =>
      cases assump_42
      case intro assump_45 assump_46 =>
        cases assump_45
        case inl assump_47 =>
          cases assump_47
          case intro assump_49 assump_50 =>
            cases assump_46
            case intro assump_55 assump_56 =>
              cases assump_55
              case intro assump_57 assump_58 =>
                apply False.elim assump_58
        case inr assump_48 =>
          cases assump_46
          case intro assump_65 assump_66 =>
            cases assump_65
            case intro assump_67 assump_68 =>
              apply False.elim assump_68


variable (p3 p2 p1 p5 p6 p4 p7 : Prop)
theorem file63_60029 : (((((p5 → False) ∨ (p3 ∧ p3)) ∨ ((p7 ∧ p4) → False)) ∧ (((p1 → False) ∧ (p7 ∨ True)) ∧ ((False → False) → (True → False)))) → ((((p5 → p2) ∧ (p6 ∧ p2)) ∧ ((p4 ∧ p5) ∨ (False → False))) → (((p6 → False) → (p2 → False)) → ((p3 ∨ True) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_2
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          cases assump_12
          case inl assump_23 =>
            cases assump_23
            case intro assump_25 assump_26 =>
              cases assump_1
              case intro assump_31 assump_32 =>
                cases assump_31
                case inl assump_33 =>
                  cases assump_33
                  case inl assump_35 =>
                    cases assump_32
                    case intro assump_39 assump_40 =>
                      cases assump_39
                      case intro assump_41 assump_42 =>
                        cases assump_42
                        case inl assump_45 =>
                          have assump_507 : (False → False) := by
                            intro assump_52
                            apply False.elim assump_52
                          let assump_51 := assump_40 assump_507
                          have assump_508 : True := by
                            apply True.intro
                          let assump_55 := assump_51 assump_508
                          apply False.elim assump_55
                        case inr assump_46 =>
                          have assump_509 : (False → False) := by
                            intro assump_64
                            apply False.elim assump_64
                          let assump_63 := assump_40 assump_509
                          have assump_510 : True := by
                            apply True.intro
                          let assump_67 := assump_63 assump_510
                          apply False.elim assump_67
                  case inr assump_36 =>
                    cases assump_36
                    case intro assump_71 assump_72 =>
                      cases assump_32
                      case intro assump_77 assump_78 =>
                        cases assump_77
                        case intro assump_79 assump_80 =>
                          cases assump_80
                          case inl assump_83 =>
                            have assump_511 : (False → False) := by
                              intro assump_90
                              apply False.elim assump_90
                            let assump_89 := assump_78 assump_511
                            have assump_512 : True := by
                              apply True.intro
                            let assump_93 := assump_89 assump_512
                            apply False.elim assump_93
                          case inr assump_84 =>
                            have assump_513 : (False → False) := by
                              intro assump_102
                              apply False.elim assump_102
                            let assump_101 := assump_78 assump_513
                            have assump_514 : True := by
                              apply True.intro
                            let assump_105 := assump_101 assump_514
                            apply False.elim assump_105
                case inr assump_34 =>
                  cases assump_32
                  case intro assump_111 assump_112 =>
                    cases assump_111
                    case intro assump_113 assump_114 =>
                      cases assump_114
                      case inl assump_117 =>
                        have assump_515 : (False → False) := by
                          intro assump_124
                          apply False.elim assump_124
                        let assump_123 := assump_112 assump_515
                        have assump_516 : True := by
                          apply True.intro
                        let assump_127 := assump_123 assump_516
                        apply False.elim assump_127
                      case inr assump_118 =>
                        have assump_517 : (False → False) := by
                          intro assump_136
                          apply False.elim assump_136
                        let assump_135 := assump_112 assump_517
                        have assump_518 : True := by
                          apply True.intro
                        let assump_139 := assump_135 assump_518
                        apply False.elim assump_139
          case inr assump_24 =>
            cases assump_1
            case intro assump_145 assump_146 =>
              cases assump_145
              case inl assump_147 =>
                cases assump_147
                case inl assump_149 =>
                  cases assump_146
                  case intro assump_153 assump_154 =>
                    cases assump_153
                    case intro assump_155 assump_156 =>
                      cases assump_156
                      case inl assump_159 =>
                        have assump_519 : (False → False) := by
                          intro assump_166
                          apply False.elim assump_166
                        let assump_165 := assump_154 assump_519
                        have assump_520 : True := by
                          apply True.intro
                        let assump_169 := assump_165 assump_520
                        apply False.elim assump_169
                      case inr assump_160 =>
                        have assump_521 : (False → False) := by
                          intro assump_178
                          apply False.elim assump_178
                        let assump_177 := assump_154 assump_521
                        have assump_522 : True := by
                          apply True.intro
                        let assump_181 := assump_177 assump_522
                        apply False.elim assump_181
                case inr assump_150 =>
                  cases assump_150
                  case intro assump_185 assump_186 =>
                    cases assump_146
                    case intro assump_191 assump_192 =>
                      cases assump_191
                      case intro assump_193 assump_194 =>
                        cases assump_194
                        case inl assump_197 =>
                          have assump_523 : (False → False) := by
                            intro assump_204
                            apply False.elim assump_204
                          let assump_203 := assump_192 assump_523
                          have assump_524 : True := by
                            apply True.intro
                          let assump_207 := assump_203 assump_524
                          apply False.elim assump_207
                        case inr assump_198 =>
                          have assump_525 : (False → False) := by
                            intro assump_216
                            apply False.elim assump_216
                          let assump_215 := assump_192 assump_525
                          have assump_526 : True := by
                            apply True.intro
                          let assump_219 := assump_215 assump_526
                          apply False.elim assump_219
              case inr assump_148 =>
                cases assump_146
                case intro assump_225 assump_226 =>
                  cases assump_225
                  case intro assump_227 assump_228 =>
                    cases assump_228
                    case inl assump_231 =>
                      have assump_527 : (False → False) := by
                        intro assump_238
                        apply False.elim assump_238
                      let assump_237 := assump_226 assump_527
                      have assump_528 : True := by
                        apply True.intro
                      let assump_241 := assump_237 assump_528
                      apply False.elim assump_241
                    case inr assump_232 =>
                      have assump_529 : (False → False) := by
                        intro assump_250
                        apply False.elim assump_250
                      let assump_249 := assump_226 assump_529
                      have assump_530 : True := by
                        apply True.intro
                      let assump_253 := assump_249 assump_530
                      apply False.elim assump_253
  case inr assump_6 =>
    cases assump_2
    case intro assump_261 assump_262 =>
      cases assump_261
      case intro assump_263 assump_264 =>
        cases assump_264
        case intro assump_267 assump_268 =>
          cases assump_262
          case inl assump_273 =>
            cases assump_273
            case intro assump_275 assump_276 =>
              cases assump_1
              case intro assump_281 assump_282 =>
                cases assump_281
                case inl assump_283 =>
                  cases assump_283
                  case inl assump_285 =>
                    cases assump_282
                    case intro assump_289 assump_290 =>
                      cases assump_289
                      case intro assump_291 assump_292 =>
                        cases assump_292
                        case inl assump_295 =>
                          have assump_531 : (False → False) := by
                            intro assump_302
                            apply False.elim assump_302
                          let assump_301 := assump_290 assump_531
                          have assump_532 : True := by
                            apply True.intro
                          let assump_305 := assump_301 assump_532
                          apply False.elim assump_305
                        case inr assump_296 =>
                          have assump_533 : (False → False) := by
                            intro assump_314
                            apply False.elim assump_314
                          let assump_313 := assump_290 assump_533
                          have assump_534 : True := by
                            apply True.intro
                          let assump_317 := assump_313 assump_534
                          apply False.elim assump_317
                  case inr assump_286 =>
                    cases assump_286
                    case intro assump_321 assump_322 =>
                      cases assump_282
                      case intro assump_327 assump_328 =>
                        cases assump_327
                        case intro assump_329 assump_330 =>
                          cases assump_330
                          case inl assump_333 =>
                            have assump_535 : (False → False) := by
                              intro assump_340
                              apply False.elim assump_340
                            let assump_339 := assump_328 assump_535
                            have assump_536 : True := by
                              apply True.intro
                            let assump_343 := assump_339 assump_536
                            apply False.elim assump_343
                          case inr assump_334 =>
                            have assump_537 : (False → False) := by
                              intro assump_352
                              apply False.elim assump_352
                            let assump_351 := assump_328 assump_537
                            have assump_538 : True := by
                              apply True.intro
                            let assump_355 := assump_351 assump_538
                            apply False.elim assump_355
                case inr assump_284 =>
                  cases assump_282
                  case intro assump_361 assump_362 =>
                    cases assump_361
                    case intro assump_363 assump_364 =>
                      cases assump_364
                      case inl assump_367 =>
                        have assump_539 : (False → False) := by
                          intro assump_374
                          apply False.elim assump_374
                        let assump_373 := assump_362 assump_539
                        have assump_540 : True := by
                          apply True.intro
                        let assump_377 := assump_373 assump_540
                        apply False.elim assump_377
                      case inr assump_368 =>
                        have assump_541 : (False → False) := by
                          intro assump_386
                          apply False.elim assump_386
                        let assump_385 := assump_362 assump_541
                        have assump_542 : True := by
                          apply True.intro
                        let assump_389 := assump_385 assump_542
                        apply False.elim assump_389
          case inr assump_274 =>
            cases assump_1
            case intro assump_395 assump_396 =>
              cases assump_395
              case inl assump_397 =>
                cases assump_397
                case inl assump_399 =>
                  cases assump_396
                  case intro assump_403 assump_404 =>
                    cases assump_403
                    case intro assump_405 assump_406 =>
                      cases assump_406
                      case inl assump_409 =>
                        have assump_543 : (False → False) := by
                          intro assump_416
                          apply False.elim assump_416
                        let assump_415 := assump_404 assump_543
                        have assump_544 : True := by
                          apply True.intro
                        let assump_419 := assump_415 assump_544
                        apply False.elim assump_419
                      case inr assump_410 =>
                        have assump_545 : (False → False) := by
                          intro assump_428
                          apply False.elim assump_428
                        let assump_427 := assump_404 assump_545
                        have assump_546 : True := by
                          apply True.intro
                        let assump_431 := assump_427 assump_546
                        apply False.elim assump_431
                case inr assump_400 =>
                  cases assump_400
                  case intro assump_435 assump_436 =>
                    cases assump_396
                    case intro assump_441 assump_442 =>
                      cases assump_441
                      case intro assump_443 assump_444 =>
                        cases assump_444
                        case inl assump_447 =>
                          have assump_547 : (False → False) := by
                            intro assump_454
                            apply False.elim assump_454
                          let assump_453 := assump_442 assump_547
                          have assump_548 : True := by
                            apply True.intro
                          let assump_457 := assump_453 assump_548
                          apply False.elim assump_457
                        case inr assump_448 =>
                          have assump_549 : (False → False) := by
                            intro assump_466
                            apply False.elim assump_466
                          let assump_465 := assump_442 assump_549
                          have assump_550 : True := by
                            apply True.intro
                          let assump_469 := assump_465 assump_550
                          apply False.elim assump_469
              case inr assump_398 =>
                cases assump_396
                case intro assump_475 assump_476 =>
                  cases assump_475
                  case intro assump_477 assump_478 =>
                    cases assump_478
                    case inl assump_481 =>
                      have assump_551 : (False → False) := by
                        intro assump_488
                        apply False.elim assump_488
                      let assump_487 := assump_476 assump_551
                      have assump_552 : True := by
                        apply True.intro
                      let assump_491 := assump_487 assump_552
                      apply False.elim assump_491
                    case inr assump_482 =>
                      have assump_553 : (False → False) := by
                        intro assump_500
                        apply False.elim assump_500
                      let assump_499 := assump_476 assump_553
                      have assump_554 : True := by
                        apply True.intro
                      let assump_503 := assump_499 assump_554
                      apply False.elim assump_503


variable (p0 p7 p2 p6 p5 p3 : Prop)
theorem file63_77187 : (((((p7 ∨ p2) → False) ∨ ((p2 ∨ True) ∨ (p0 ∧ p5))) → (((p3 → p0) → (p0 → p3)) ∨ ((p0 ∧ p7) → (False ∨ p6)))) → ((((False → p2) → False) → False) ∨ (((p7 → False) ∨ (p0 ∨ p6)) ∧ ((p2 → p3) → False)))) := by
  intro assump_21
  apply Or.inl
  intro assump_24
  have assump_34 : (False → p2) := by
    intro assump_28
    apply False.elim assump_28
  let assump_27 := assump_24 assump_34
  apply False.elim assump_27


variable (p0 p7 p2 p1 p6 p4 : Prop)
theorem file63_77662 : ((((((p7 → True) ∨ (p1 → False)) ∧ ((True ∧ p2) ∨ (p4 ∨ p0))) ∨ (((p6 → True) → False) ∨ ((p6 ∧ p4) ∨ (p2 ∧ p2)))) ∧ ((((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case inl assump_12 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              have assump_240 : (((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) := by
                apply And.intro
                intro assump_23
                cases assump_23
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
                intro assump_30
                have assump_241 : True := by
                  apply True.intro
                let assump_33 := assump_30 assump_241
                apply False.elim assump_33
              let assump_22 := assump_3 assump_240
              apply False.elim assump_22
          case inr assump_13 =>
            cases assump_13
            case inl assump_40 =>
              have assump_242 : (((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) := by
                apply And.intro
                intro assump_47
                cases assump_47
                case intro assump_48 assump_49 =>
                  apply False.elim assump_49
                intro assump_54
                have assump_243 : True := by
                  apply True.intro
                let assump_57 := assump_54 assump_243
                apply False.elim assump_57
              let assump_46 := assump_3 assump_242
              apply False.elim assump_46
            case inr assump_41 =>
              have assump_244 : (((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) := by
                apply And.intro
                intro assump_69
                cases assump_69
                case intro assump_70 assump_71 =>
                  apply False.elim assump_71
                intro assump_76
                have assump_245 : True := by
                  apply True.intro
                let assump_79 := assump_76 assump_245
                apply False.elim assump_79
              let assump_68 := assump_3 assump_244
              apply False.elim assump_68
        case inr assump_9 =>
          cases assump_7
          case inl assump_88 =>
            cases assump_88
            case intro assump_90 assump_91 =>
              have assump_246 : (((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) := by
                apply And.intro
                intro assump_99
                cases assump_99
                case intro assump_100 assump_101 =>
                  apply False.elim assump_101
                intro assump_106
                have assump_247 : True := by
                  apply True.intro
                let assump_109 := assump_106 assump_247
                apply False.elim assump_109
              let assump_98 := assump_3 assump_246
              apply False.elim assump_98
          case inr assump_89 =>
            cases assump_89
            case inl assump_116 =>
              have assump_248 : (((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) := by
                apply And.intro
                intro assump_123
                cases assump_123
                case intro assump_124 assump_125 =>
                  apply False.elim assump_125
                intro assump_130
                have assump_249 : True := by
                  apply True.intro
                let assump_133 := assump_130 assump_249
                apply False.elim assump_133
              let assump_122 := assump_3 assump_248
              apply False.elim assump_122
            case inr assump_117 =>
              have assump_250 : (((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) := by
                apply And.intro
                intro assump_145
                cases assump_145
                case intro assump_146 assump_147 =>
                  apply False.elim assump_147
                intro assump_152
                have assump_251 : True := by
                  apply True.intro
                let assump_155 := assump_152 assump_251
                apply False.elim assump_155
              let assump_144 := assump_3 assump_250
              apply False.elim assump_144
    case inr assump_5 =>
      cases assump_5
      case inl assump_162 =>
        have assump_252 : (((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) := by
          apply And.intro
          intro assump_169
          cases assump_169
          case intro assump_170 assump_171 =>
            apply False.elim assump_171
          intro assump_176
          have assump_253 : True := by
            apply True.intro
          let assump_179 := assump_176 assump_253
          apply False.elim assump_179
        let assump_168 := assump_3 assump_252
        apply False.elim assump_168
      case inr assump_163 =>
        cases assump_163
        case inl assump_186 =>
          cases assump_186
          case intro assump_188 assump_189 =>
            have assump_254 : (((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) := by
              apply And.intro
              intro assump_197
              cases assump_197
              case intro assump_198 assump_199 =>
                apply False.elim assump_199
              intro assump_204
              have assump_255 : True := by
                apply True.intro
              let assump_207 := assump_204 assump_255
              apply False.elim assump_207
            let assump_196 := assump_3 assump_254
            apply False.elim assump_196
        case inr assump_187 =>
          cases assump_187
          case intro assump_214 assump_215 =>
            have assump_256 : (((p0 ∧ False) → (False ∨ False)) ∧ ((True → False) → False)) := by
              apply And.intro
              intro assump_223
              cases assump_223
              case intro assump_224 assump_225 =>
                apply False.elim assump_225
              intro assump_230
              have assump_257 : True := by
                apply True.intro
              let assump_233 := assump_230 assump_257
              apply False.elim assump_233
            let assump_222 := assump_3 assump_256
            apply False.elim assump_222


variable (p4 p7 p3 p1 : Prop)
theorem file63_84290 : (((((p3 → False) → (True → False)) ∧ ((p3 ∧ True) ∧ (p3 ∧ False))) → False) ∨ ((((False → p4) ∨ (p1 → False)) ∧ ((p7 → False) → (False → p1))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_15


variable (p1 p6 p3 p4 p5 : Prop)
theorem file63_84805 : (((((p1 ∧ p1) → False) ∨ ((p4 → False) ∨ (p3 ∧ False))) → False) → ((((True → False) → False) ∨ ((False ∨ p6) ∧ (p1 → p1))) ∨ (((p3 → p3) → (p5 ∧ p1)) → ((p5 → False) → False)))) := by
  intro assump_28
  apply Or.inl
  apply Or.inl
  intro assump_31
  have assump_38 : True := by
    apply True.intro
  let assump_34 := assump_31 assump_38
  apply False.elim assump_34


variable (p0 : Prop)
theorem file63_85220 : (((((True ∧ False) ∧ (False → p0)) → False) → False) → False) := by
  intro assump_5
  have assump_21 : (((True ∧ False) ∧ (False → p0)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
  let assump_8 := assump_5 assump_21
  apply False.elim assump_8


variable (p0 p5 p3 p1 p7 : Prop)
theorem file63_85667 : (((((p1 ∨ p3) ∧ (p5 ∨ p5)) ∧ ((p3 → False) → (p5 ∧ p5))) ∧ (((p7 ∨ p3) ∨ (p1 ∨ p0)) → False)) → False) := by
  intro assump_56
  cases assump_56
  case intro assump_57 assump_58 =>
    cases assump_57
    case intro assump_59 assump_60 =>
      cases assump_59
      case intro assump_61 assump_62 =>
        cases assump_61
        case inl assump_63 =>
          cases assump_62
          case inl assump_67 =>
            have assump_113 : ((p7 ∨ p3) ∨ (p1 ∨ p0)) := by
              apply Or.inr
              apply Or.inl
              exact assump_63
            let assump_75 := assump_58 assump_113
            apply False.elim assump_75
          case inr assump_68 =>
            have assump_114 : ((p7 ∨ p3) ∨ (p1 ∨ p0)) := by
              apply Or.inr
              apply Or.inl
              exact assump_63
            let assump_85 := assump_58 assump_114
            apply False.elim assump_85
        case inr assump_64 =>
          cases assump_62
          case inl assump_91 =>
            have assump_115 : ((p7 ∨ p3) ∨ (p1 ∨ p0)) := by
              apply Or.inl
              apply Or.inr
              exact assump_64
            let assump_99 := assump_58 assump_115
            apply False.elim assump_99
          case inr assump_92 =>
            have assump_116 : ((p7 ∨ p3) ∨ (p1 ∨ p0)) := by
              apply Or.inl
              apply Or.inr
              exact assump_64
            let assump_109 := assump_58 assump_116
            apply False.elim assump_109


variable (p0 p3 p1 p5 p7 p6 : Prop)
theorem file63_87226 : (((((p1 → False) → False) → ((p1 ∧ p1) → (p3 ∨ True))) → False) → ((((p0 ∨ True) ∨ (p6 → False)) → False) ∨ (((False → p5) → False) → ((p7 ∧ p3) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      have assump_59 : (((p1 → False) → False) → ((p1 ∧ p1) → (p3 ∨ True))) := by
        intro assump_13
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          apply Or.inr
          apply True.intro
      let assump_12 := assump_1 assump_59
      apply False.elim assump_12
    case inr assump_8 =>
      have assump_60 : (((p1 → False) → False) → ((p1 ∧ p1) → (p3 ∨ True))) := by
        intro assump_29
        intro assump_30
        cases assump_30
        case intro assump_31 assump_32 =>
          apply Or.inr
          apply True.intro
      let assump_28 := assump_1 assump_60
      apply False.elim assump_28
  case inr assump_6 =>
    have assump_61 : (((p1 → False) → False) → ((p1 ∧ p1) → (p3 ∨ True))) := by
      intro assump_46
      intro assump_47
      cases assump_47
      case intro assump_48 assump_49 =>
        apply Or.inr
        apply True.intro
    let assump_45 := assump_1 assump_61
    apply False.elim assump_45


variable (p5 p3 p6 p4 p7 p1 p0 : Prop)
theorem file63_88578 : (((((p1 ∨ False) → (True ∨ p6)) → ((True ∧ False) ∨ (False ∧ p5))) → (((False ∨ p1) ∧ (p3 ∨ p0)) ∨ ((p3 → False) ∨ (p0 ∨ True)))) ∧ ((((p4 ∨ p3) → (p6 ∨ p5)) → ((p3 → False) → False)) → (((p3 ∧ p4) → (p3 ∨ p0)) ∨ ((p0 ∧ p7) ∨ (False → p7))))) := by
  apply And.intro
  intro assump_13
  apply Or.inr
  apply Or.inl
  intro assump_16
  have assump_51 : ((p1 ∨ False) → (True ∨ p6)) := by
    intro assump_21
    cases assump_21
    case inl assump_22 =>
      apply Or.inl
      apply True.intro
    case inr assump_23 =>
      apply False.elim assump_23
  let assump_20 := assump_13 assump_51
  cases assump_20
  case inl assump_29 =>
    cases assump_29
    case intro assump_31 assump_32 =>
      apply False.elim assump_32
  case inr assump_30 =>
    cases assump_30
    case intro assump_37 assump_38 =>
      apply False.elim assump_37
  intro assump_41
  apply Or.inl
  intro assump_44
  cases assump_44
  case intro assump_45 assump_46 =>
    apply Or.inl
    exact assump_45


variable (p2 p5 p6 p0 p3 p7 p4 p1 : Prop)
theorem file63_89627 : (((((p4 ∨ p7) → (p6 → False)) ∧ ((p7 → p5) ∨ (p7 → False))) → (((True → False) ∧ (True → p2)) → False)) ∨ ((((p3 → p0) ∨ (p1 ∨ p1)) ∧ ((True ∨ p2) → (p5 ∧ p4))) ∨ (((p4 → p0) → False) ∧ ((p7 → p6) ∨ (p5 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        have assump_35 : True := by
          apply True.intro
        let assump_21 := assump_3 assump_35
        apply False.elim assump_21
      case inr assump_14 =>
        have assump_36 : True := by
          apply True.intro
        let assump_31 := assump_3 assump_36
        apply False.elim assump_31


variable (p1 p4 p7 p3 p6 p5 p2 p0 : Prop)
theorem file63_90433 : (((((p7 ∨ p5) → (p2 ∧ p0)) → ((p3 ∧ p2) → (p6 → p5))) → (((False ∧ p5) → False) ∨ ((p4 → p6) → (p7 ∧ p3)))) ∨ ((((p5 ∨ False) → False) → ((p0 ∧ p1) → (p5 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p0 p5 p1 p6 p7 p2 : Prop)
theorem file63_90819 : ((((((p2 ∧ p6) ∧ (False → False)) → False) → False) ∧ ((((p2 → False) ∨ (p2 ∨ p2)) ∧ ((False → p7) ∨ (p1 ∨ False))) ∧ (((p0 ∨ p0) ∨ (p0 → p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            have assump_134 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
              apply Or.inr
              intro assump_21
              have assump_135 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                apply Or.inl
                apply Or.inl
                exact assump_21
              let assump_25 := assump_7 assump_135
              apply False.elim assump_25
            let assump_20 := assump_7 assump_134
            apply False.elim assump_20
          case inr assump_15 =>
            cases assump_15
            case inl assump_32 =>
              have assump_136 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                apply Or.inr
                intro assump_39
                have assump_137 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_39
                let assump_43 := assump_7 assump_137
                apply False.elim assump_43
              let assump_38 := assump_7 assump_136
              apply False.elim assump_38
            case inr assump_33 =>
              apply False.elim assump_33
        case inr assump_11 =>
          cases assump_11
          case inl assump_52 =>
            cases assump_9
            case inl assump_56 =>
              have assump_138 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                apply Or.inr
                intro assump_63
                have assump_139 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_63
                let assump_67 := assump_7 assump_139
                apply False.elim assump_67
              let assump_62 := assump_7 assump_138
              apply False.elim assump_62
            case inr assump_57 =>
              cases assump_57
              case inl assump_74 =>
                have assump_140 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                  apply Or.inr
                  intro assump_81
                  have assump_141 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                    apply Or.inl
                    apply Or.inl
                    exact assump_81
                  let assump_85 := assump_7 assump_141
                  apply False.elim assump_85
                let assump_80 := assump_7 assump_140
                apply False.elim assump_80
              case inr assump_75 =>
                apply False.elim assump_75
          case inr assump_53 =>
            cases assump_9
            case inl assump_96 =>
              have assump_142 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                apply Or.inr
                intro assump_103
                have assump_143 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_103
                let assump_107 := assump_7 assump_143
                apply False.elim assump_107
              let assump_102 := assump_7 assump_142
              apply False.elim assump_102
            case inr assump_97 =>
              cases assump_97
              case inl assump_114 =>
                have assump_144 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                  apply Or.inr
                  intro assump_121
                  have assump_145 : ((p0 ∨ p0) ∨ (p0 → p5)) := by
                    apply Or.inl
                    apply Or.inl
                    exact assump_121
                  let assump_125 := assump_7 assump_145
                  apply False.elim assump_125
                let assump_120 := assump_7 assump_144
                apply False.elim assump_120
              case inr assump_115 =>
                apply False.elim assump_115


variable (p4 p0 p6 p2 p3 p5 p1 : Prop)
theorem file63_94975 : (((((p5 → p5) → False) ∧ ((p1 → False) ∧ (p5 ∧ p2))) → (((p0 → False) → False) → False)) ∧ ((((False ∧ p3) ∧ (p4 → False)) ∧ ((p5 ∨ False) ∧ (p1 ∨ p4))) → (((p2 ∨ p6) ∨ (p2 → p3)) → ((p3 → False) → (True ∨ True))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        have assump_68 : (p5 → p5) := by
          intro assump_23
          exact assump_23
        let assump_22 := assump_5 assump_68
        apply False.elim assump_22
  intro assump_29
  intro assump_30
  intro assump_31
  cases assump_30
  case inl assump_34 =>
    cases assump_34
    case inl assump_36 =>
      cases assump_29
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            apply False.elim assump_44
    case inr assump_37 =>
      cases assump_29
      case intro assump_50 assump_51 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            apply False.elim assump_54
  case inr assump_35 =>
    cases assump_29
    case intro assump_60 assump_61 =>
      cases assump_60
      case intro assump_62 assump_63 =>
        cases assump_62
        case intro assump_64 assump_65 =>
          apply False.elim assump_64


variable (p7 p2 p0 p5 p3 p6 : Prop)
theorem file63_96539 : (((((False → False) → (p7 → False)) → False) → (((p6 ∧ True) → (p3 ∨ p2)) → False)) → ((((p5 ∧ p3) ∧ (p2 ∨ p2)) ∨ ((p7 → p7) → False)) → (((False ∧ p6) → (p0 → False)) → ((True ∧ p3) → (True ∨ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_2
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          cases assump_16
          case inl assump_23 =>
            apply Or.inl
            apply True.intro
          case inr assump_24 =>
            apply Or.inl
            apply True.intro
    case inr assump_14 =>
      apply Or.inl
      apply True.intro


variable (p7 p5 p3 p1 p2 : Prop)
theorem file63_97361 : (((((p2 → False) → (False ∧ p1)) → ((False ∧ p7) → (p3 ∨ p5))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p2 → False) → (False ∧ p1)) → ((False ∧ p7) → (p3 ∨ p5))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p0 p3 p1 p6 p4 p5 p2 : Prop)
theorem file63_97804 : (((((p1 ∨ p5) ∨ (p4 ∧ p2)) ∧ ((p1 → False) → (p4 → False))) ∧ (((p6 ∧ p5) ∨ (True ∨ True)) → False)) → ((((p1 → False) ∨ (p1 ∨ p2)) ∧ ((p3 → False) → False)) ∨ (((p0 ∧ p2) → (p1 → p3)) → ((p4 ∧ p3) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inl
          apply And.intro
          apply Or.inl
          intro assump_16
          have assump_80 : ((p6 ∧ p5) ∨ (True ∨ True)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_20 := assump_3 assump_80
          apply False.elim assump_20
          intro assump_24
          have assump_81 : ((p6 ∧ p5) ∨ (True ∨ True)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_28 := assump_3 assump_81
          apply False.elim assump_28
        case inr assump_9 =>
          apply Or.inl
          apply And.intro
          apply Or.inl
          intro assump_38
          have assump_82 : ((p6 ∧ p5) ∨ (True ∨ True)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_42 := assump_3 assump_82
          apply False.elim assump_42
          intro assump_46
          have assump_83 : ((p6 ∧ p5) ∨ (True ∨ True)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_50 := assump_3 assump_83
          apply False.elim assump_50
      case inr assump_7 =>
        cases assump_7
        case intro assump_54 assump_55 =>
          apply Or.inl
          apply And.intro
          apply Or.inl
          intro assump_64
          have assump_84 : ((p6 ∧ p5) ∨ (True ∨ True)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_68 := assump_3 assump_84
          apply False.elim assump_68
          intro assump_72
          have assump_85 : ((p6 ∧ p5) ∨ (True ∨ True)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_76 := assump_3 assump_85
          apply False.elim assump_76


variable (p7 p0 p5 p2 p1 p3 p4 : Prop)
theorem file63_100137 : ((((((p1 ∨ p1) ∨ (p2 → p0)) ∧ ((True ∧ p5) ∧ (p4 → p0))) → (((p7 → False) ∨ (p1 ∧ False)) ∨ ((p3 → False) ∨ (False ∨ p5)))) ∧ ((((p1 ∧ p3) ∧ (p3 → False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_27 : (((p1 ∧ p3) ∧ (p3 → False)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_28 : p3 := by
            exact assump_13
          let assump_20 := assump_11 assump_28
          apply False.elim assump_20
    let assump_8 := assump_3 assump_27
    apply False.elim assump_8


variable (p0 p7 p1 p4 p2 p3 p6 : Prop)
theorem file63_100886 : (((((p6 ∧ False) ∧ (p4 → p4)) → ((p4 → False) ∧ (True ∧ p4))) ∨ (((p4 ∨ p1) → (False → False)) ∨ ((p1 → p1) → (p0 ∨ p0)))) ∨ ((((p0 → p1) → (p7 ∨ p3)) → False) → (((p1 ∧ p1) → (p4 → p6)) ∧ ((p2 ∧ p0) ∧ (True → p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  apply And.intro
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
  apply And.intro
  apply True.intro
  cases assump_5
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      apply False.elim assump_20


variable (p6 p5 p4 : Prop)
theorem file63_101566 : (((((p5 → p5) → False) → ((p6 → p4) → False)) → False) → False) := by
  intro assump_1
  have assump_21 : (((p5 → p5) → False) → ((p6 → p4) → False)) := by
    intro assump_5
    intro assump_6
    have assump_22 : (p5 → p5) := by
      intro assump_12
      exact assump_12
    let assump_11 := assump_5 assump_22
    apply False.elim assump_11
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p2 p0 p6 p7 : Prop)
theorem file63_102031 : (((((p7 → p6) → (True ∨ p2)) ∨ ((True → p6) ∧ (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p7 → p6) → (True ∨ p2)) ∨ ((True → p6) ∧ (p0 → False))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p6 p1 p0 p3 p7 p5 p4 : Prop)
theorem file63_102422 : (((((p6 → False) → (p4 ∨ True)) ∨ ((p1 → p6) ∧ (p1 ∧ p5))) ∨ (((p1 ∧ p1) ∧ (p7 → False)) ∨ ((p7 ∧ p0) → (p2 → False)))) → ((((p2 ∧ False) ∨ (p3 ∧ p3)) → ((p6 ∧ p0) ∧ (True → p4))) → (((False ∨ p1) → (True ∨ p7)) ∨ ((p7 ∧ p7) ∨ (p6 → p3))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      intro assump_11
      cases assump_11
      case inl assump_12 =>
        apply False.elim assump_12
      case inr assump_13 =>
        apply Or.inl
        apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_18 assump_19 =>
        cases assump_19
        case intro assump_22 assump_23 =>
          apply Or.inl
          intro assump_28
          cases assump_28
          case inl assump_29 =>
            apply False.elim assump_29
          case inr assump_30 =>
            apply Or.inl
            apply True.intro
  case inr assump_6 =>
    cases assump_6
    case inl assump_35 =>
      cases assump_35
      case intro assump_37 assump_38 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          apply Or.inl
          intro assump_47
          cases assump_47
          case inl assump_48 =>
            apply False.elim assump_48
          case inr assump_49 =>
            apply Or.inl
            apply True.intro
    case inr assump_36 =>
      apply Or.inl
      intro assump_56
      cases assump_56
      case inl assump_57 =>
        apply False.elim assump_57
      case inr assump_58 =>
        apply Or.inl
        apply True.intro


variable (p2 p7 p5 p6 p3 p1 : Prop)
theorem file63_104085 : (((((p5 ∨ p6) ∨ (p7 → p6)) → ((p2 ∨ p1) → (p5 → False))) ∧ (((True ∨ p7) ∧ (False ∧ p2)) ∧ ((False → p2) ∨ (p3 ∨ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
        case inr assump_11 =>
          cases assump_9
          case intro assump_20 assump_21 =>
            apply False.elim assump_20


variable (p5 p2 p1 : Prop)
theorem file63_104752 : (((((False ∨ True) ∨ (p5 → p2)) ∨ ((p1 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : (((False ∨ True) ∨ (p5 → p2)) ∨ ((p1 → False) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p6 p5 p4 p0 p3 p7 p1 : Prop)
theorem file63_105133 : ((((((True → p4) → (False ∨ p7)) ∧ ((p2 → p3) ∧ (p6 → False))) ∧ (((p1 → p0) ∧ (p4 → False)) ∨ ((p1 ∨ p4) ∨ (p2 → p2)))) ∧ ((((p4 → p4) ∨ (p4 → False)) ∨ ((p1 → p5) → (False ∧ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_5
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_70 : (((p4 → p4) ∨ (p4 → False)) ∨ ((p1 → p5) → (False ∧ p3))) := by
                apply Or.inl
                apply Or.inl
                intro assump_27
                exact assump_27
              let assump_26 := assump_3 assump_70
              apply False.elim assump_26
          case inr assump_17 =>
            cases assump_17
            case inl assump_33 =>
              cases assump_33
              case inl assump_35 =>
                have assump_71 : (((p4 → p4) ∨ (p4 → False)) ∨ ((p1 → p5) → (False ∧ p3))) := by
                  apply Or.inl
                  apply Or.inl
                  intro assump_42
                  exact assump_42
                let assump_41 := assump_3 assump_71
                apply False.elim assump_41
              case inr assump_36 =>
                have assump_72 : (((p4 → p4) ∨ (p4 → False)) ∨ ((p1 → p5) → (False ∧ p3))) := by
                  apply Or.inl
                  apply Or.inl
                  intro assump_53
                  exact assump_53
                let assump_52 := assump_3 assump_72
                apply False.elim assump_52
            case inr assump_34 =>
              have assump_73 : (((p4 → p4) ∨ (p4 → False)) ∨ ((p1 → p5) → (False ∧ p3))) := by
                apply Or.inl
                apply Or.inl
                intro assump_64
                exact assump_64
              let assump_63 := assump_3 assump_73
              apply False.elim assump_63


variable (p6 p3 p2 p5 p1 p0 p4 : Prop)
theorem file63_107271 : (((((False → True) → False) ∨ ((p0 → p2) ∨ (p3 → False))) → (((p4 ∨ p4) ∧ (True → False)) → ((p4 → False) → (p2 → p6)))) ∨ ((((True ∨ p5) ∧ (p5 → p0)) → False) ∨ (((p1 ∨ p4) → False) → False))) := by
  apply Or.inl
  intro assump_18
  intro assump_19
  intro assump_20
  intro assump_21
  cases assump_19
  case intro assump_26 assump_27 =>
    cases assump_26
    case inl assump_28 =>
      cases assump_18
      case inl assump_34 =>
        have assump_88 : (False → True) := by
          intro assump_39
          apply True.intro
        let assump_38 := assump_34 assump_88
        apply False.elim assump_38
      case inr assump_35 =>
        cases assump_35
        case inl assump_43 =>
          have assump_89 : True := by
            apply True.intro
          let assump_48 := assump_27 assump_89
          apply False.elim assump_48
        case inr assump_44 =>
          have assump_90 : True := by
            apply True.intro
          let assump_55 := assump_27 assump_90
          apply False.elim assump_55
    case inr assump_29 =>
      cases assump_18
      case inl assump_63 =>
        have assump_91 : (False → True) := by
          intro assump_68
          apply True.intro
        let assump_67 := assump_63 assump_91
        apply False.elim assump_67
      case inr assump_64 =>
        cases assump_64
        case inl assump_72 =>
          have assump_92 : True := by
            apply True.intro
          let assump_77 := assump_27 assump_92
          apply False.elim assump_77
        case inr assump_73 =>
          have assump_93 : True := by
            apply True.intro
          let assump_84 := assump_27 assump_93
          apply False.elim assump_84


variable (p5 p6 p3 p7 p4 : Prop)
theorem file63_109027 : (((((p4 ∧ False) → (p5 → False)) → ((False ∧ False) → False)) ∨ (((p3 → p3) → False) ∧ ((p5 ∧ False) ∨ (p3 ∨ False)))) → ((((p7 ∧ p7) ∧ (p3 ∧ p4)) ∧ ((p6 → False) ∧ (p4 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case intro assump_13 assump_14 =>
          cases assump_4
          case intro assump_19 assump_20 =>
            cases assump_1
            case inl assump_25 =>
              have assump_71 : p4 := by
                exact assump_14
              let assump_41 := assump_20 assump_71
              apply False.elim assump_41
            case inr assump_26 =>
              cases assump_26
              case intro assump_45 assump_46 =>
                cases assump_46
                case inl assump_49 =>
                  cases assump_49
                  case intro assump_51 assump_52 =>
                    apply False.elim assump_52
                case inr assump_50 =>
                  cases assump_50
                  case inl assump_57 =>
                    have assump_72 : (p3 → p3) := by
                      intro assump_63
                      exact assump_63
                    let assump_62 := assump_45 assump_72
                    apply False.elim assump_62
                  case inr assump_58 =>
                    apply False.elim assump_58


variable (p7 : Prop)
theorem file63_110573 : ((((((True → p7) → (p7 ∧ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((True → p7) → (p7 ∧ True)) → False) → False) := by
    intro assump_5
    have assump_21 : ((True → p7) → (p7 ∧ True)) := by
      intro assump_9
      apply And.intro
      have assump_22 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_22
      exact assump_12
      apply True.intro
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p0 p4 p6 p2 p5 p7 : Prop)
theorem file63_111194 : (((((p5 ∧ p0) ∧ (False ∧ p6)) ∧ ((p0 → p4) ∨ (True ∧ p5))) → False) ∨ ((((True → False) ∨ (p2 → p0)) → False) → (((False ∧ p7) → False) ∨ ((p2 ∨ p6) ∧ (p7 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p2 p7 p6 p4 p1 p5 p3 p0 : Prop)
theorem file63_111730 : (((((p0 ∨ p5) ∨ (p2 ∧ p6)) → False) → (((p0 → p2) ∧ (True → False)) → False)) ∨ ((((True → True) ∨ (p2 → p4)) ∨ ((p3 ∧ p4) → False)) ∧ (((p3 → False) ∨ (p7 ∨ p1)) ∧ ((p6 ∧ True) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_16 : True := by
      apply True.intro
    let assump_12 := assump_4 assump_16
    apply False.elim assump_12


variable (p2 p4 p5 p3 p0 p7 : Prop)
theorem file63_112212 : ((((((p0 ∨ False) ∧ (p7 ∨ p5)) → ((p4 → False) → False)) → False) ∧ ((((False ∧ p4) ∨ (False → False)) → False) ∧ (((p3 ∧ p3) ∧ (True → False)) → ((p2 → p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_20 : ((False ∧ p4) ∨ (False → False)) := by
        apply Or.inr
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_6 assump_20
      apply False.elim assump_13


variable (p2 p4 p7 p1 p5 : Prop)
theorem file63_112793 : (((((False ∨ p5) ∧ (p7 → p4)) ∨ ((p2 ∨ p2) → (p2 ∨ p1))) → False) → False) := by
  intro assump_14
  have assump_28 : (((False ∨ p5) ∧ (p7 → p4)) ∨ ((p2 ∨ p2) → (p2 ∨ p1))) := by
    apply Or.inr
    intro assump_18
    cases assump_18
    case inl assump_19 =>
      apply Or.inl
      exact assump_19
    case inr assump_20 =>
      apply Or.inl
      exact assump_20
  let assump_17 := assump_14 assump_28
  apply False.elim assump_17


variable (p7 p6 p2 p0 p5 p4 p1 : Prop)
theorem file63_113294 : ((((((p4 → False) → (p4 → False)) ∨ ((p4 ∨ p6) → False)) ∧ (((p6 ∨ True) ∨ (p7 ∧ p6)) → False)) ∧ ((((True ∧ p5) → False) ∨ ((p5 ∧ p2) → False)) ∧ (((p1 ∧ p0) ∨ (p5 → False)) ∨ ((p7 → False) ∨ (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case inl assump_18 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  have assump_204 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                  let assump_31 := assump_5 assump_204
                  apply False.elim assump_31
              case inr assump_21 =>
                have assump_205 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_39 := assump_5 assump_205
                apply False.elim assump_39
            case inr assump_19 =>
              cases assump_19
              case inl assump_43 =>
                have assump_206 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_49 := assump_5 assump_206
                apply False.elim assump_49
              case inr assump_44 =>
                have assump_207 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_57 := assump_5 assump_207
                apply False.elim assump_57
          case inr assump_15 =>
            cases assump_13
            case inl assump_63 =>
              cases assump_63
              case inl assump_65 =>
                cases assump_65
                case intro assump_67 assump_68 =>
                  have assump_208 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                  let assump_76 := assump_5 assump_208
                  apply False.elim assump_76
              case inr assump_66 =>
                have assump_209 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_84 := assump_5 assump_209
                apply False.elim assump_84
            case inr assump_64 =>
              cases assump_64
              case inl assump_88 =>
                have assump_210 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_94 := assump_5 assump_210
                apply False.elim assump_94
              case inr assump_89 =>
                have assump_211 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_102 := assump_5 assump_211
                apply False.elim assump_102
      case inr assump_7 =>
        cases assump_3
        case intro assump_110 assump_111 =>
          cases assump_110
          case inl assump_112 =>
            cases assump_111
            case inl assump_116 =>
              cases assump_116
              case inl assump_118 =>
                cases assump_118
                case intro assump_120 assump_121 =>
                  have assump_212 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                  let assump_129 := assump_5 assump_212
                  apply False.elim assump_129
              case inr assump_119 =>
                have assump_213 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_137 := assump_5 assump_213
                apply False.elim assump_137
            case inr assump_117 =>
              cases assump_117
              case inl assump_141 =>
                have assump_214 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_147 := assump_5 assump_214
                apply False.elim assump_147
              case inr assump_142 =>
                have assump_215 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_155 := assump_5 assump_215
                apply False.elim assump_155
          case inr assump_113 =>
            cases assump_111
            case inl assump_161 =>
              cases assump_161
              case inl assump_163 =>
                cases assump_163
                case intro assump_165 assump_166 =>
                  have assump_216 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                  let assump_174 := assump_5 assump_216
                  apply False.elim assump_174
              case inr assump_164 =>
                have assump_217 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_182 := assump_5 assump_217
                apply False.elim assump_182
            case inr assump_162 =>
              cases assump_162
              case inl assump_186 =>
                have assump_218 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_192 := assump_5 assump_218
                apply False.elim assump_192
              case inr assump_187 =>
                have assump_219 : ((p6 ∨ True) ∨ (p7 ∧ p6)) := by
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_200 := assump_5 assump_219
                apply False.elim assump_200


variable (p3 p5 p4 p1 p0 : Prop)
theorem file63_119851 : ((((((p0 ∧ p1) ∨ (p3 → False)) ∨ ((p5 → True) → False)) → False) ∧ ((((p4 ∧ True) → (p5 → p4)) → ((True ∨ p0) ∨ (True → p0))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_19 : (((p4 ∧ True) → (p5 → p4)) → ((True ∨ p0) ∨ (True → p0))) := by
      intro assump_13
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_12 := assump_7 assump_19
    apply False.elim assump_12


variable (p0 p5 p3 p6 p2 p1 p7 : Prop)
theorem file63_120372 : ((((((p3 ∧ False) → (p1 ∧ p7)) ∧ ((p5 → False) → (p1 ∨ p0))) → (((True → p7) ∨ (p2 → False)) ∧ ((p3 → False) → (p1 ∧ p1)))) ∧ ((((p6 → p6) → False) → ((p2 ∧ p1) ∧ (p5 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_43 : (((p6 → p6) → False) → ((p2 ∧ p1) ∧ (p5 → False))) := by
      intro assump_9
      apply And.intro
      apply And.intro
      have assump_44 : (p6 → p6) := by
        intro assump_13
        exact assump_13
      let assump_12 := assump_9 assump_44
      apply False.elim assump_12
      have assump_45 : (p6 → p6) := by
        intro assump_22
        exact assump_22
      let assump_21 := assump_9 assump_45
      apply False.elim assump_21
      intro assump_28
      have assump_46 : (p6 → p6) := by
        intro assump_34
        exact assump_34
      let assump_33 := assump_9 assump_46
      apply False.elim assump_33
    let assump_8 := assump_3 assump_43
    apply False.elim assump_8


variable (p2 p4 p5 p6 : Prop)
theorem file63_121417 : ((((((p4 ∨ p5) ∧ (p6 ∧ False)) ∧ ((True ∨ p2) ∧ (p6 ∨ p6))) → False) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p4 ∨ p5) ∧ (p6 ∧ False)) ∧ ((True ∨ p2) ∧ (p6 ∨ p6))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
        case inr assump_11 =>
          cases assump_9
          case intro assump_22 assump_23 =>
            apply False.elim assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p3 p4 p6 p7 p2 p5 p1 : Prop)
theorem file63_122179 : (((((p7 ∨ p2) ∧ (p4 ∧ p5)) ∨ ((p4 → p3) → (p7 → False))) ∧ (((p5 → False) → (p5 → p4)) → False)) → ((((True ∨ p5) → (p6 → p6)) ∨ ((p7 ∧ p3) → False)) → (((True ∨ p7) ∨ (True ∨ p1)) → False))) := by
  intro assump_14
  intro assump_15
  intro assump_16
  cases assump_16
  case inl assump_17 =>
    cases assump_17
    case inl assump_19 =>
      cases assump_15
      case inl assump_23 =>
        cases assump_14
        case intro assump_27 assump_28 =>
          cases assump_27
          case inl assump_29 =>
            cases assump_29
            case intro assump_31 assump_32 =>
              cases assump_31
              case inl assump_33 =>
                cases assump_32
                case intro assump_37 assump_38 =>
                  have assump_583 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_46
                    intro assump_47
                    exact assump_37
                  let assump_45 := assump_28 assump_583
                  apply False.elim assump_45
              case inr assump_34 =>
                cases assump_32
                case intro assump_57 assump_58 =>
                  have assump_584 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_66
                    intro assump_67
                    exact assump_57
                  let assump_65 := assump_28 assump_584
                  apply False.elim assump_65
          case inr assump_30 =>
            have assump_585 : ((p5 → False) → (p5 → p4)) := by
              intro assump_80
              intro assump_81
              have assump_586 : p5 := by
                exact assump_81
              let assump_86 := assump_80 assump_586
              apply False.elim assump_86
            let assump_79 := assump_28 assump_585
            apply False.elim assump_79
      case inr assump_24 =>
        cases assump_14
        case intro assump_95 assump_96 =>
          cases assump_95
          case inl assump_97 =>
            cases assump_97
            case intro assump_99 assump_100 =>
              cases assump_99
              case inl assump_101 =>
                cases assump_100
                case intro assump_105 assump_106 =>
                  have assump_587 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_114
                    intro assump_115
                    exact assump_105
                  let assump_113 := assump_96 assump_587
                  apply False.elim assump_113
              case inr assump_102 =>
                cases assump_100
                case intro assump_125 assump_126 =>
                  have assump_588 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_134
                    intro assump_135
                    exact assump_125
                  let assump_133 := assump_96 assump_588
                  apply False.elim assump_133
          case inr assump_98 =>
            have assump_589 : ((p5 → False) → (p5 → p4)) := by
              intro assump_148
              intro assump_149
              have assump_590 : p5 := by
                exact assump_149
              let assump_154 := assump_148 assump_590
              apply False.elim assump_154
            let assump_147 := assump_96 assump_589
            apply False.elim assump_147
    case inr assump_20 =>
      cases assump_15
      case inl assump_163 =>
        cases assump_14
        case intro assump_167 assump_168 =>
          cases assump_167
          case inl assump_169 =>
            cases assump_169
            case intro assump_171 assump_172 =>
              cases assump_171
              case inl assump_173 =>
                cases assump_172
                case intro assump_177 assump_178 =>
                  have assump_591 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_186
                    intro assump_187
                    exact assump_177
                  let assump_185 := assump_168 assump_591
                  apply False.elim assump_185
              case inr assump_174 =>
                cases assump_172
                case intro assump_197 assump_198 =>
                  have assump_592 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_206
                    intro assump_207
                    exact assump_197
                  let assump_205 := assump_168 assump_592
                  apply False.elim assump_205
          case inr assump_170 =>
            have assump_593 : ((p5 → False) → (p5 → p4)) := by
              intro assump_220
              intro assump_221
              have assump_594 : p5 := by
                exact assump_221
              let assump_226 := assump_220 assump_594
              apply False.elim assump_226
            let assump_219 := assump_168 assump_593
            apply False.elim assump_219
      case inr assump_164 =>
        cases assump_14
        case intro assump_235 assump_236 =>
          cases assump_235
          case inl assump_237 =>
            cases assump_237
            case intro assump_239 assump_240 =>
              cases assump_239
              case inl assump_241 =>
                cases assump_240
                case intro assump_245 assump_246 =>
                  have assump_595 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_254
                    intro assump_255
                    exact assump_245
                  let assump_253 := assump_236 assump_595
                  apply False.elim assump_253
              case inr assump_242 =>
                cases assump_240
                case intro assump_265 assump_266 =>
                  have assump_596 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_274
                    intro assump_275
                    exact assump_265
                  let assump_273 := assump_236 assump_596
                  apply False.elim assump_273
          case inr assump_238 =>
            have assump_597 : ((p5 → False) → (p5 → p4)) := by
              intro assump_288
              intro assump_289
              have assump_598 : p5 := by
                exact assump_289
              let assump_294 := assump_288 assump_598
              apply False.elim assump_294
            let assump_287 := assump_236 assump_597
            apply False.elim assump_287
  case inr assump_18 =>
    cases assump_18
    case inl assump_301 =>
      cases assump_15
      case inl assump_305 =>
        cases assump_14
        case intro assump_309 assump_310 =>
          cases assump_309
          case inl assump_311 =>
            cases assump_311
            case intro assump_313 assump_314 =>
              cases assump_313
              case inl assump_315 =>
                cases assump_314
                case intro assump_319 assump_320 =>
                  have assump_599 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_328
                    intro assump_329
                    exact assump_319
                  let assump_327 := assump_310 assump_599
                  apply False.elim assump_327
              case inr assump_316 =>
                cases assump_314
                case intro assump_339 assump_340 =>
                  have assump_600 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_348
                    intro assump_349
                    exact assump_339
                  let assump_347 := assump_310 assump_600
                  apply False.elim assump_347
          case inr assump_312 =>
            have assump_601 : ((p5 → False) → (p5 → p4)) := by
              intro assump_362
              intro assump_363
              have assump_602 : p5 := by
                exact assump_363
              let assump_368 := assump_362 assump_602
              apply False.elim assump_368
            let assump_361 := assump_310 assump_601
            apply False.elim assump_361
      case inr assump_306 =>
        cases assump_14
        case intro assump_377 assump_378 =>
          cases assump_377
          case inl assump_379 =>
            cases assump_379
            case intro assump_381 assump_382 =>
              cases assump_381
              case inl assump_383 =>
                cases assump_382
                case intro assump_387 assump_388 =>
                  have assump_603 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_396
                    intro assump_397
                    exact assump_387
                  let assump_395 := assump_378 assump_603
                  apply False.elim assump_395
              case inr assump_384 =>
                cases assump_382
                case intro assump_407 assump_408 =>
                  have assump_604 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_416
                    intro assump_417
                    exact assump_407
                  let assump_415 := assump_378 assump_604
                  apply False.elim assump_415
          case inr assump_380 =>
            have assump_605 : ((p5 → False) → (p5 → p4)) := by
              intro assump_430
              intro assump_431
              have assump_606 : p5 := by
                exact assump_431
              let assump_436 := assump_430 assump_606
              apply False.elim assump_436
            let assump_429 := assump_378 assump_605
            apply False.elim assump_429
    case inr assump_302 =>
      cases assump_15
      case inl assump_445 =>
        cases assump_14
        case intro assump_449 assump_450 =>
          cases assump_449
          case inl assump_451 =>
            cases assump_451
            case intro assump_453 assump_454 =>
              cases assump_453
              case inl assump_455 =>
                cases assump_454
                case intro assump_459 assump_460 =>
                  have assump_607 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_468
                    intro assump_469
                    exact assump_459
                  let assump_467 := assump_450 assump_607
                  apply False.elim assump_467
              case inr assump_456 =>
                cases assump_454
                case intro assump_479 assump_480 =>
                  have assump_608 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_488
                    intro assump_489
                    exact assump_479
                  let assump_487 := assump_450 assump_608
                  apply False.elim assump_487
          case inr assump_452 =>
            have assump_609 : ((p5 → False) → (p5 → p4)) := by
              intro assump_502
              intro assump_503
              have assump_610 : p5 := by
                exact assump_503
              let assump_508 := assump_502 assump_610
              apply False.elim assump_508
            let assump_501 := assump_450 assump_609
            apply False.elim assump_501
      case inr assump_446 =>
        cases assump_14
        case intro assump_517 assump_518 =>
          cases assump_517
          case inl assump_519 =>
            cases assump_519
            case intro assump_521 assump_522 =>
              cases assump_521
              case inl assump_523 =>
                cases assump_522
                case intro assump_527 assump_528 =>
                  have assump_611 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_536
                    intro assump_537
                    exact assump_527
                  let assump_535 := assump_518 assump_611
                  apply False.elim assump_535
              case inr assump_524 =>
                cases assump_522
                case intro assump_547 assump_548 =>
                  have assump_612 : ((p5 → False) → (p5 → p4)) := by
                    intro assump_556
                    intro assump_557
                    exact assump_547
                  let assump_555 := assump_518 assump_612
                  apply False.elim assump_555
          case inr assump_520 =>
            have assump_613 : ((p5 → False) → (p5 → p4)) := by
              intro assump_570
              intro assump_571
              have assump_614 : p5 := by
                exact assump_571
              let assump_576 := assump_570 assump_614
              apply False.elim assump_576
            let assump_569 := assump_518 assump_613
            apply False.elim assump_569


variable (p5 p3 p1 p4 p0 p7 p6 : Prop)
theorem file63_134719 : (((((p4 ∧ p5) → False) → ((p3 → False) ∧ (p7 → False))) → (((p3 ∧ p3) ∧ (p7 → False)) ∨ ((p1 ∧ p5) → (False ∨ p1)))) ∨ ((((p5 → False) ∧ (False → False)) → False) ∧ (((p6 ∧ p7) ∧ (True ∨ p7)) ∨ ((p1 ∧ p0) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inr
    exact assump_5


variable (p6 p0 p4 p7 p5 p3 : Prop)
theorem file63_135153 : ((((((p0 ∨ p6) ∨ (p3 → p5)) → ((p7 ∨ True) ∧ (p5 → False))) → (((p4 → False) → (p4 → False)) ∨ ((p5 → False) → (True → False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p0 ∨ p6) ∨ (p3 → p5)) → ((p7 ∨ True) ∧ (p5 → False))) → (((p4 → False) → (p4 → False)) ∨ ((p5 → False) → (True → False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_22 : p4 := by
      exact assump_9
    let assump_14 := assump_8 assump_22
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p6 p4 : Prop)
theorem file63_135784 : ((((((False ∧ False) → False) → ((True ∧ True) → (p6 ∧ True))) → (((p4 → False) ∧ (False ∧ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False ∧ False) → False) → ((True ∧ True) → (p6 ∧ True))) → (((p4 → False) ∧ (False ∧ p4)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p3 p4 p0 p2 p5 p1 : Prop)
theorem file63_136377 : ((((((p4 → p1) ∨ (p2 ∧ p0)) ∧ ((p2 → p5) ∧ (True → False))) ∧ (((p2 ∨ p7) ∧ (False ∧ False)) → False)) ∨ ((((p4 → False) → (p2 → p3)) ∧ ((p3 ∧ True) ∧ (p4 ∨ p3))) ∧ (((p1 ∨ p3) ∨ (p1 → False)) → False))) → False) := by
  intro assump_16
  cases assump_16
  case inl assump_17 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_21
        case inl assump_23 =>
          cases assump_22
          case intro assump_27 assump_28 =>
            have assump_91 : True := by
              apply True.intro
            let assump_36 := assump_28 assump_91
            apply False.elim assump_36
        case inr assump_24 =>
          cases assump_24
          case intro assump_40 assump_41 =>
            cases assump_22
            case intro assump_46 assump_47 =>
              have assump_92 : True := by
                apply True.intro
              let assump_55 := assump_47 assump_92
              apply False.elim assump_55
  case inr assump_18 =>
    cases assump_18
    case intro assump_59 assump_60 =>
      cases assump_59
      case intro assump_61 assump_62 =>
        cases assump_62
        case intro assump_65 assump_66 =>
          cases assump_65
          case intro assump_67 assump_68 =>
            cases assump_66
            case inl assump_73 =>
              have assump_93 : ((p1 ∨ p3) ∨ (p1 → False)) := by
                apply Or.inl
                apply Or.inr
                exact assump_67
              let assump_79 := assump_60 assump_93
              apply False.elim assump_79
            case inr assump_74 =>
              have assump_94 : ((p1 ∨ p3) ∨ (p1 → False)) := by
                apply Or.inl
                apply Or.inr
                exact assump_74
              let assump_87 := assump_60 assump_94
              apply False.elim assump_87


variable (p1 p2 p0 p3 p5 p6 p4 : Prop)
theorem file63_138331 : (((((p2 ∨ True) → False) → ((p2 → p3) → False)) → (((p5 → p0) ∨ (p2 → False)) ∧ ((p0 → False) ∨ (p2 → False)))) → ((((True → False) ∧ (p6 ∧ p2)) → False) ∨ (((p1 ∨ p4) → (p1 → False)) ∧ ((p0 → p0) ∨ (p5 ∨ p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_21 : True := by
        apply True.intro
      let assump_17 := assump_5 assump_21
      apply False.elim assump_17


variable (p3 p7 p1 p4 p5 : Prop)
theorem file63_138897 : (((((p5 → True) → False) ∨ ((True ∨ False) → False)) → (((p1 ∧ p3) ∨ (True ∧ p1)) ∨ ((p4 → False) ∨ (p1 → False)))) ∨ ((((False → False) → (p3 → p7)) → ((p7 → p3) → False)) ∨ (((p1 → False) → (p4 → p5)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    apply Or.inl
    intro assump_6
    have assump_25 : (p5 → True) := by
      intro assump_11
      apply True.intro
    let assump_10 := assump_2 assump_25
    apply False.elim assump_10
  case inr assump_3 =>
    apply Or.inr
    apply Or.inl
    intro assump_17
    have assump_26 : (True ∨ False) := by
      apply Or.inl
      apply True.intro
    let assump_21 := assump_3 assump_26
    apply False.elim assump_21


variable (p1 p4 p0 p6 p7 p5 p2 : Prop)
theorem file63_139692 : (((((True → p5) → False) ∨ ((p4 ∧ p6) → False)) ∧ (((p4 → False) ∧ (p2 ∨ p7)) ∧ ((p6 → False) ∧ (False ∨ True)))) → ((((p4 → p1) ∨ (p1 ∨ False)) → ((p5 ∨ p0) → False)) → (((False → False) → False) → ((False → p4) ∨ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_9
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_17
          case inl assump_20 =>
            cases assump_15
            case intro assump_24 assump_25 =>
              cases assump_25
              case inl assump_28 =>
                apply False.elim assump_28
              case inr assump_29 =>
                apply Or.inl
                intro assump_34
                apply False.elim assump_34
          case inr assump_21 =>
            cases assump_15
            case intro assump_39 assump_40 =>
              cases assump_40
              case inl assump_43 =>
                apply False.elim assump_43
              case inr assump_44 =>
                apply Or.inl
                intro assump_49
                apply False.elim assump_49
    case inr assump_11 =>
      cases assump_9
      case intro assump_54 assump_55 =>
        cases assump_54
        case intro assump_56 assump_57 =>
          cases assump_57
          case inl assump_60 =>
            cases assump_55
            case intro assump_64 assump_65 =>
              cases assump_65
              case inl assump_68 =>
                apply False.elim assump_68
              case inr assump_69 =>
                apply Or.inl
                intro assump_74
                apply False.elim assump_74
          case inr assump_61 =>
            cases assump_55
            case intro assump_79 assump_80 =>
              cases assump_80
              case inl assump_83 =>
                apply False.elim assump_83
              case inr assump_84 =>
                apply Or.inl
                intro assump_89
                apply False.elim assump_89


variable (p5 p6 p0 p1 p4 p2 p3 p7 : Prop)
theorem file63_141895 : (((((False → False) → (p4 ∧ p4)) → ((p6 → False) ∧ (p3 ∧ p3))) → (((p7 → p3) ∨ (p6 → False)) → ((p3 ∨ True) ∧ (p4 ∧ False)))) → ((((False ∧ p1) ∧ (p2 → False)) ∧ ((p0 ∧ p1) ∨ (True ∨ False))) → (((p6 → False) ∧ (p5 ∧ False)) → ((p3 ∧ p0) ∨ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case intro assump_8 assump_9 =>
      apply False.elim assump_9


variable (p3 p0 p4 : Prop)
theorem file63_142398 : (((((False → False) → False) → ((p4 ∨ p4) ∧ (p3 ∨ p0))) → False) → False) := by
  intro assump_1
  have assump_27 : (((False → False) → False) → ((p4 ∨ p4) ∧ (p3 ∨ p0))) := by
    intro assump_5
    apply And.intro
    have assump_28 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_28
    apply False.elim assump_8
    have assump_29 : (False → False) := by
      intro assump_18
      apply False.elim assump_18
    let assump_17 := assump_5 assump_29
    apply False.elim assump_17
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


