variable (p4 p6 p2 p7 p0 p1 p5 p3 : Prop)
theorem file37_50 : (((((p6 → p4) ∧ (p0 → False)) ∨ ((p2 → False) ∧ (p0 → p4))) ∧ (((True → False) → False) → ((p7 ∧ p7) → (p4 ∧ p2)))) → ((((p3 ∧ p5) → False) → ((p6 → p4) → (False ∧ True))) → (((False → p0) ∧ (True ∨ p1)) ∨ ((False ∨ p1) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply Or.inl
        apply And.intro
        intro assump_17
        apply False.elim assump_17
        apply Or.inl
        apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_20 assump_21 =>
        apply Or.inl
        apply And.intro
        intro assump_28
        apply False.elim assump_28
        apply Or.inl
        apply True.intro


variable (p0 p5 p1 p7 p6 p4 : Prop)
theorem file37_923 : (((((p6 ∨ p5) ∨ (p1 ∧ p6)) ∧ ((p0 ∨ True) ∧ (p4 → p6))) → False) → ((((False → False) → False) ∨ ((p5 ∨ False) ∧ (p0 ∧ p6))) → (((p6 ∨ p7) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    have assump_43 : (False → False) := by
      intro assump_14
      apply False.elim assump_14
    let assump_13 := assump_6 assump_43
    apply False.elim assump_13
  case inr assump_7 =>
    cases assump_7
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_21
        case intro assump_26 assump_27 =>
          have assump_44 : (((p6 ∨ p5) ∨ (p1 ∧ p6)) ∧ ((p0 ∨ True) ∧ (p4 → p6))) := by
            apply And.intro
            apply Or.inl
            apply Or.inl
            exact assump_27
            apply And.intro
            apply Or.inl
            exact assump_26
            intro assump_35
            exact assump_27
          let assump_34 := assump_1 assump_44
          apply False.elim assump_34
      case inr assump_23 =>
        apply False.elim assump_23


variable (p3 p7 p1 p5 p2 p6 p0 : Prop)
theorem file37_2083 : (((((p0 ∧ False) → False) → False) → False) ∨ ((((p1 → False) → False) ∧ ((p2 ∨ p1) ∨ (p7 → False))) ∨ (((p5 ∨ p3) → False) → ((p6 → False) ∨ (p3 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p0 ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p1 p0 p5 p2 : Prop)
theorem file37_2553 : ((((((p0 ∧ p1) → (p4 → False)) → False) → (((True → False) → False) ∨ ((p2 → p5) ∧ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 ∧ p1) → (p4 → False)) → False) → (((True → False) → False) ∨ ((p2 → p5) ∧ (p1 → False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p6 p7 p0 p4 p1 p3 : Prop)
theorem file37_3124 : (((((p7 ∨ p3) → False) ∧ ((True ∨ p7) → (False → p6))) ∧ (((p5 ∧ p7) ∧ (p4 → False)) ∧ ((p1 → False) ∧ (p6 ∨ p0)))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_21
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            cases assump_29
            case intro assump_40 assump_41 =>
              cases assump_41
              case inl assump_44 =>
                have assump_72 : (p7 ∨ p3) := by
                  apply Or.inl
                  exact assump_33
                let assump_55 := assump_22 assump_72
                apply False.elim assump_55
              case inr assump_45 =>
                have assump_73 : (p7 ∨ p3) := by
                  apply Or.inl
                  exact assump_33
                let assump_68 := assump_22 assump_73
                apply False.elim assump_68


variable (p0 p6 p4 p1 p3 p7 p2 p5 : Prop)
theorem file37_4245 : (((((False → False) → False) ∧ ((p5 → True) → (p7 ∧ p5))) → (((p5 → False) ∧ (p6 → False)) ∨ ((p7 ∨ False) ∨ (p7 → False)))) ∧ ((((p0 ∧ p1) → (False → p2)) ∨ ((p2 → False) ∧ (p3 → False))) ∨ (((p7 ∧ p7) → False) → ((p4 → False) → False)))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_8
    have assump_44 : (False → False) := by
      intro assump_18
      apply False.elim assump_18
    let assump_17 := assump_2 assump_44
    apply False.elim assump_17
    intro assump_24
    have assump_45 : (False → False) := by
      intro assump_34
      apply False.elim assump_34
    let assump_33 := assump_2 assump_45
    apply False.elim assump_33
  apply Or.inl
  apply Or.inl
  intro assump_40
  intro assump_41
  apply False.elim assump_41


variable (p7 p1 : Prop)
theorem file37_5134 : (((((p7 → p1) → False) ∨ ((p1 → False) → False)) ∧ (((p1 → False) → (True ∨ True)) → False)) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case inl assump_15 =>
      have assump_39 : ((p1 → False) → (True ∨ True)) := by
        intro assump_22
        apply Or.inl
        apply True.intro
      let assump_21 := assump_14 assump_39
      apply False.elim assump_21
    case inr assump_16 =>
      have assump_40 : ((p1 → False) → (True ∨ True)) := by
        intro assump_33
        apply Or.inl
        apply True.intro
      let assump_32 := assump_14 assump_40
      apply False.elim assump_32


variable (p1 p7 p4 p6 p0 p2 : Prop)
theorem file37_5858 : (((((True → True) ∨ (p6 → False)) ∧ ((True ∨ p7) ∧ (p0 → p7))) → False) → ((((False ∨ p2) ∧ (True → False)) → ((True ∨ p0) → (p1 ∧ p0))) ∨ (((p7 ∧ p4) → False) ∧ ((p1 → p0) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply And.intro
  cases assump_5
  case inl assump_6 =>
    cases assump_4
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        apply False.elim assump_12
      case inr assump_13 =>
        have assump_70 : True := by
          apply True.intro
        let assump_20 := assump_11 assump_70
        apply False.elim assump_20
  case inr assump_7 =>
    cases assump_4
    case intro assump_26 assump_27 =>
      cases assump_26
      case inl assump_28 =>
        apply False.elim assump_28
      case inr assump_29 =>
        have assump_71 : True := by
          apply True.intro
        let assump_36 := assump_27 assump_71
        apply False.elim assump_36
  cases assump_5
  case inl assump_40 =>
    cases assump_4
    case intro assump_44 assump_45 =>
      cases assump_44
      case inl assump_46 =>
        apply False.elim assump_46
      case inr assump_47 =>
        have assump_72 : True := by
          apply True.intro
        let assump_54 := assump_45 assump_72
        apply False.elim assump_54
  case inr assump_41 =>
    cases assump_4
    case intro assump_60 assump_61 =>
      cases assump_60
      case inl assump_62 =>
        apply False.elim assump_62
      case inr assump_63 =>
        exact assump_41


variable (p7 p3 p0 p1 p5 p2 p4 p6 : Prop)
theorem file37_7460 : ((((((p4 ∨ p0) ∧ (p1 → True)) ∨ ((True ∨ p4) ∧ (p7 → True))) → False) ∧ ((((p2 ∧ p5) ∨ (p6 → False)) ∧ ((p4 ∨ p7) ∧ (p7 → p5))) ∨ (((p3 ∧ p5) ∧ (True ∨ p0)) ∨ ((p5 → False) ∧ (p7 ∧ p5))))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_9
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_15
            case intro assump_24 assump_25 =>
              cases assump_24
              case inl assump_26 =>
                have assump_133 : (((p4 ∨ p0) ∧ (p1 → True)) ∨ ((True ∨ p4) ∧ (p7 → True))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  exact assump_26
                  intro assump_37
                  apply True.intro
                let assump_36 := assump_8 assump_133
                apply False.elim assump_36
              case inr assump_27 =>
                have assump_134 : (((p4 ∨ p0) ∧ (p1 → True)) ∨ ((True ∨ p4) ∧ (p7 → True))) := by
                  apply Or.inr
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  intro assump_51
                  apply True.intro
                let assump_50 := assump_8 assump_134
                apply False.elim assump_50
        case inr assump_17 =>
          cases assump_15
          case intro assump_57 assump_58 =>
            cases assump_57
            case inl assump_59 =>
              have assump_135 : (((p4 ∨ p0) ∧ (p1 → True)) ∨ ((True ∨ p4) ∧ (p7 → True))) := by
                apply Or.inl
                apply And.intro
                apply Or.inl
                exact assump_59
                intro assump_69
                apply True.intro
              let assump_68 := assump_8 assump_135
              apply False.elim assump_68
            case inr assump_60 =>
              have assump_136 : (((p4 ∨ p0) ∧ (p1 → True)) ∨ ((True ∨ p4) ∧ (p7 → True))) := by
                apply Or.inr
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_82
                apply True.intro
              let assump_81 := assump_8 assump_136
              apply False.elim assump_81
    case inr assump_13 =>
      cases assump_13
      case inl assump_86 =>
        cases assump_86
        case intro assump_88 assump_89 =>
          cases assump_88
          case intro assump_90 assump_91 =>
            cases assump_89
            case inl assump_96 =>
              have assump_137 : (((p4 ∨ p0) ∧ (p1 → True)) ∨ ((True ∨ p4) ∧ (p7 → True))) := by
                apply Or.inr
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_103
                apply True.intro
              let assump_102 := assump_8 assump_137
              apply False.elim assump_102
            case inr assump_97 =>
              have assump_138 : (((p4 ∨ p0) ∧ (p1 → True)) ∨ ((True ∨ p4) ∧ (p7 → True))) := by
                apply Or.inl
                apply And.intro
                apply Or.inr
                exact assump_97
                intro assump_113
                apply True.intro
              let assump_112 := assump_8 assump_138
              apply False.elim assump_112
      case inr assump_87 =>
        cases assump_87
        case intro assump_117 assump_118 =>
          cases assump_118
          case intro assump_121 assump_122 =>
            have assump_139 : p5 := by
              exact assump_122
            let assump_129 := assump_117 assump_139
            apply False.elim assump_129


variable (p5 p1 p2 p0 : Prop)
theorem file37_11323 : (((((p5 ∨ p2) ∨ (True → True)) ∨ ((p0 → False) ∧ (True ∧ False))) ∧ (((True → False) → (False → False)) → ((True → False) ∧ (p1 ∨ True)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_62 : ((True → False) → (False → False)) := by
            intro assump_15
            intro assump_16
            apply False.elim assump_16
          let assump_14 := assump_3 assump_62
          let assump_19 := And.left assump_14
          have assump_63 : True := by
            apply True.intro
          let assump_20 := assump_19 assump_63
          apply False.elim assump_20
        case inr assump_9 =>
          have assump_64 : ((True → False) → (False → False)) := by
            intro assump_29
            intro assump_30
            apply False.elim assump_30
          let assump_28 := assump_3 assump_64
          let assump_33 := And.left assump_28
          have assump_65 : True := by
            apply True.intro
          let assump_34 := assump_33 assump_65
          apply False.elim assump_34
      case inr assump_7 =>
        have assump_66 : ((True → False) → (False → False)) := by
          intro assump_43
          intro assump_44
          apply False.elim assump_44
        let assump_42 := assump_3 assump_66
        let assump_47 := And.left assump_42
        have assump_67 : True := by
          apply True.intro
        let assump_48 := assump_47 assump_67
        apply False.elim assump_48
    case inr assump_5 =>
      cases assump_5
      case intro assump_52 assump_53 =>
        cases assump_53
        case intro assump_56 assump_57 =>
          apply False.elim assump_57


variable (p3 p6 p1 p7 : Prop)
theorem file37_13186 : ((((((p3 ∧ p1) → False) ∧ ((p1 → False) ∧ (p6 → True))) → (((p3 ∨ p6) → (False → False)) ∨ ((p7 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p3 ∧ p1) → False) ∧ ((p1 → False) ∧ (p6 → True))) → (((p3 ∨ p6) → (False → False)) ∨ ((p7 → False) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_16
        intro assump_17
        apply False.elim assump_17
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p7 p0 p3 p4 p5 p1 p2 p6 : Prop)
theorem file37_13852 : (((((p5 ∧ p2) ∧ (p6 ∨ p7)) ∧ ((p6 → False) ∨ (p3 → p4))) → (((p4 → False) → False) → ((p5 → False) → (True ∧ p2)))) ∨ ((((p3 ∧ p1) → (p7 → False)) ∨ ((p0 ∧ p3) → (p1 ∨ p0))) ∧ (((p5 ∧ p2) ∧ (p7 ∧ True)) ∨ ((p4 → p6) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply True.intro
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case inl assump_18 =>
          cases assump_9
          case inl assump_22 =>
            exact assump_13
          case inr assump_23 =>
            exact assump_13
        case inr assump_19 =>
          cases assump_9
          case inl assump_30 =>
            exact assump_13
          case inr assump_31 =>
            exact assump_13


variable (p1 p3 p4 p2 p6 p5 p0 p7 : Prop)
theorem file37_14799 : (((((p2 → p3) ∧ (True → False)) ∧ ((p4 → False) ∨ (p4 ∧ p1))) → False) ∨ ((((p3 → False) → (True → p5)) ∨ ((p6 ∧ p1) → (p7 → p7))) → (((p5 → False) → (p0 ∨ True)) ∨ ((p0 ∨ True) ∨ (False ∧ p4))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        have assump_31 : True := by
          apply True.intro
        let assump_15 := assump_5 assump_31
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case intro assump_19 assump_20 =>
          have assump_32 : True := by
            apply True.intro
          let assump_27 := assump_5 assump_32
          apply False.elim assump_27


variable (p2 p7 p0 : Prop)
theorem file37_15626 : (((((p0 ∧ p7) ∧ (True → False)) → False) → False) → ((((False → p0) → False) ∨ ((p2 ∨ p7) ∧ (p7 → False))) → False)) := by
  intro assump_9
  intro assump_10
  cases assump_10
  case inl assump_11 =>
    have assump_90 : (((p0 ∧ p7) ∧ (True → False)) → False) := by
      intro assump_18
      cases assump_18
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          have assump_91 : True := by
            apply True.intro
          let assump_29 := assump_20 assump_91
          apply False.elim assump_29
    let assump_17 := assump_9 assump_90
    apply False.elim assump_17
  case inr assump_12 =>
    cases assump_12
    case intro assump_36 assump_37 =>
      cases assump_36
      case inl assump_38 =>
        have assump_92 : (((p0 ∧ p7) ∧ (True → False)) → False) := by
          intro assump_47
          cases assump_47
          case intro assump_48 assump_49 =>
            cases assump_48
            case intro assump_50 assump_51 =>
              have assump_93 : True := by
                apply True.intro
              let assump_58 := assump_49 assump_93
              apply False.elim assump_58
        let assump_46 := assump_9 assump_92
        apply False.elim assump_46
      case inr assump_39 =>
        have assump_94 : (((p0 ∧ p7) ∧ (True → False)) → False) := by
          intro assump_72
          cases assump_72
          case intro assump_73 assump_74 =>
            cases assump_73
            case intro assump_75 assump_76 =>
              have assump_95 : True := by
                apply True.intro
              let assump_83 := assump_74 assump_95
              apply False.elim assump_83
        let assump_71 := assump_9 assump_94
        apply False.elim assump_71


variable (p4 p0 p2 p1 p6 p5 p3 : Prop)
theorem file37_17459 : (((((True → True) ∧ (p1 ∨ p0)) ∧ ((p1 ∨ p4) ∧ (p2 → False))) ∨ (((p4 ∨ True) → False) → ((p1 → False) → (False ∨ p1)))) ∨ ((((p5 → p0) → (p4 ∧ p3)) ∧ ((p3 → False) ∨ (p2 → False))) ∧ (((p4 ∨ p6) ∧ (True → False)) → False))) := by
  apply Or.inl
  apply Or.inr
  intro assump_2
  intro assump_3
  have assump_12 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_8 := assump_2 assump_12
  apply False.elim assump_8


variable (p4 p5 p2 p1 p3 p0 p6 : Prop)
theorem file37_17956 : (((((p4 ∧ p0) → False) → False) → (((p2 ∨ True) ∨ (p3 ∧ False)) → ((p6 ∧ p6) ∨ (False → False)))) ∨ ((((p3 → False) → (p0 → False)) ∧ ((True ∨ p3) → (p5 → False))) → (((p1 → p3) → False) ∧ ((p1 → False) ∧ (p3 ∧ p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inr
      intro assump_11
      apply False.elim assump_11
    case inr assump_6 =>
      apply Or.inr
      intro assump_18
      apply False.elim assump_18
  case inr assump_4 =>
    cases assump_4
    case intro assump_21 assump_22 =>
      apply False.elim assump_22


variable (p4 p2 p6 p3 p7 p5 p1 : Prop)
theorem file37_18663 : (((((p3 → p6) → (p6 ∨ p3)) ∧ ((False → p4) → False)) → False) ∧ ((((p4 ∧ p2) ∧ (False ∧ False)) → ((p1 ∨ p5) ∨ (p3 → p4))) ∨ (((p1 ∧ True) → False) → ((True ∧ True) ∨ (p7 → p3))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (False → p4) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_28
    apply False.elim assump_8
  apply Or.inl
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_17
      case intro assump_24 assump_25 =>
        apply False.elim assump_24


variable (p7 p6 p4 p3 p5 p0 p2 : Prop)
theorem file37_19403 : ((((((p7 → False) ∧ (p2 ∨ p4)) → False) → (((p6 ∧ p6) → False) → ((p6 → p0) → (p0 ∧ p7)))) ∧ ((((p3 → p0) → (False ∨ True)) ∨ ((p5 → False) ∨ (True ∧ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p3 → p0) → (False ∨ True)) ∨ ((p5 → False) ∨ (True ∧ p6))) := by
      apply Or.inl
      intro assump_9
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p6 p5 p3 p4 p0 p2 : Prop)
theorem file37_19952 : (((((True → False) → (p0 ∨ True)) ∧ ((p2 ∨ p4) ∨ (p2 ∧ True))) → False) → ((((p4 → False) ∧ (p3 → False)) → ((p5 → p2) → (p2 → False))) ∨ (((p6 ∧ True) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_4
  case intro assump_11 assump_12 =>
    have assump_28 : (((True → False) → (p0 ∨ True)) ∧ ((p2 ∨ p4) ∨ (p2 ∧ True))) := by
      apply And.intro
      intro assump_22
      apply Or.inr
      apply True.intro
      apply Or.inl
      apply Or.inl
      exact assump_6
    let assump_21 := assump_1 assump_28
    apply False.elim assump_21


variable (p1 : Prop)
theorem file37_20615 : ((((((p1 ∧ False) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p1 ∧ False) → False) → False) → False) := by
    intro assump_5
    have assump_23 : ((p1 ∧ False) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p3 p6 p1 p5 p0 p7 : Prop)
theorem file37_21152 : (((((p3 → False) ∧ (True ∧ p3)) → ((p5 → p5) → (p6 → False))) ∧ (((p2 ∨ p7) ∧ (True ∨ p0)) ∨ ((False → p3) → False))) → ((((False ∧ p3) ∨ (p7 ∧ p1)) ∧ ((True ∧ p1) ∧ (p2 → False))) → (((p0 ∧ False) ∧ (p1 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p7 : Prop)
theorem file37_21617 : ((((((False ∨ True) ∨ (False → p7)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∨ True) ∨ (False → p7)) → False) → False) := by
    intro assump_5
    have assump_16 : ((False ∨ True) ∨ (False → p7)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p1 p0 p4 p5 p6 p2 p7 : Prop)
theorem file37_22128 : (((((p1 ∨ False) ∨ (p7 → False)) → ((p1 ∨ False) ∨ (False ∨ p0))) ∧ (((p3 ∧ p4) ∨ (p4 → False)) ∧ ((p4 → False) ∧ (p6 ∨ p5)))) → ((((p0 ∧ True) → False) ∨ ((p6 → False) → False)) → (((True → False) → False) → ((p1 ∨ True) ∨ (p2 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_15
            case intro assump_24 assump_25 =>
              cases assump_25
              case inl assump_28 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
              case inr assump_29 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
        case inr assump_17 =>
          cases assump_15
          case intro assump_36 assump_37 =>
            cases assump_37
            case inl assump_40 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
            case inr assump_41 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
  case inr assump_7 =>
    cases assump_1
    case intro assump_48 assump_49 =>
      cases assump_49
      case intro assump_52 assump_53 =>
        cases assump_52
        case inl assump_54 =>
          cases assump_54
          case intro assump_56 assump_57 =>
            cases assump_53
            case intro assump_62 assump_63 =>
              cases assump_63
              case inl assump_66 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
              case inr assump_67 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
        case inr assump_55 =>
          cases assump_53
          case intro assump_74 assump_75 =>
            cases assump_75
            case inl assump_78 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
            case inr assump_79 =>
              apply Or.inl
              apply Or.inr
              apply True.intro


variable (p5 p4 p3 p2 p7 p0 p6 : Prop)
theorem file37_24486 : (((((p3 → p6) → False) → False) → (((False → True) ∨ (p7 ∨ p2)) ∧ ((False ∧ p5) → False))) ∨ ((((p7 → p7) ∨ (p5 → p0)) → ((p5 ∧ p6) ∧ (p4 ∧ p3))) → (((p6 → False) → False) ∨ ((p7 → False) → (p7 ∧ p4))))) := by
  apply Or.inl
  intro assump_18
  apply And.intro
  apply Or.inl
  intro assump_21
  apply True.intro
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    apply False.elim assump_23


variable (p5 p0 p3 p7 p2 : Prop)
theorem file37_24959 : (((((p2 ∨ True) → (p3 ∨ p3)) → False) → False) → ((((False ∧ p7) ∧ (p2 → p3)) → False) ∨ (((p5 ∨ p3) ∨ (False → False)) ∨ ((p3 ∨ p0) ∨ (p3 → p5))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_7


variable (p2 p3 p0 p4 p5 p6 p1 p7 : Prop)
theorem file37_25367 : (((((p0 ∧ p7) ∧ (p7 → p3)) → ((p1 → False) → (False → p4))) ∨ (((p5 → p0) → (p0 → p1)) → ((p4 → False) → (False → p2)))) ∨ ((((p3 ∧ p3) → (p6 → False)) → ((p2 → False) ∨ (True ∨ False))) → (((p0 → p0) ∧ (p1 → p2)) ∨ ((p3 → False) ∨ (p0 ∨ p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p3 p7 p4 p2 p6 p5 : Prop)
theorem file37_25788 : ((((((False → False) ∧ (p6 → True)) ∨ ((p5 → False) ∧ (p2 ∨ True))) ∧ (((True ∨ False) → False) → False)) ∧ ((((p3 → p7) ∧ (p7 → False)) ∧ ((p3 → True) → False)) ∨ (((p3 ∧ p4) ∧ (p4 ∨ p4)) ∧ ((True → False) ∧ (False → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                have assump_195 : (p3 → True) := by
                  intro assump_29
                  apply True.intro
                let assump_28 := assump_19 assump_195
                apply False.elim assump_28
          case inr assump_17 =>
            cases assump_17
            case intro assump_33 assump_34 =>
              cases assump_33
              case intro assump_35 assump_36 =>
                cases assump_35
                case intro assump_37 assump_38 =>
                  cases assump_36
                  case inl assump_43 =>
                    cases assump_34
                    case intro assump_47 assump_48 =>
                      have assump_196 : True := by
                        apply True.intro
                      let assump_54 := assump_47 assump_196
                      apply False.elim assump_54
                  case inr assump_44 =>
                    cases assump_34
                    case intro assump_60 assump_61 =>
                      have assump_197 : True := by
                        apply True.intro
                      let assump_67 := assump_60 assump_197
                      apply False.elim assump_67
      case inr assump_7 =>
        cases assump_7
        case intro assump_71 assump_72 =>
          cases assump_72
          case inl assump_75 =>
            cases assump_3
            case inl assump_81 =>
              cases assump_81
              case intro assump_83 assump_84 =>
                cases assump_83
                case intro assump_85 assump_86 =>
                  have assump_198 : (p3 → True) := by
                    intro assump_94
                    apply True.intro
                  let assump_93 := assump_84 assump_198
                  apply False.elim assump_93
            case inr assump_82 =>
              cases assump_82
              case intro assump_98 assump_99 =>
                cases assump_98
                case intro assump_100 assump_101 =>
                  cases assump_100
                  case intro assump_102 assump_103 =>
                    cases assump_101
                    case inl assump_108 =>
                      cases assump_99
                      case intro assump_112 assump_113 =>
                        have assump_199 : True := by
                          apply True.intro
                        let assump_119 := assump_112 assump_199
                        apply False.elim assump_119
                    case inr assump_109 =>
                      cases assump_99
                      case intro assump_125 assump_126 =>
                        have assump_200 : True := by
                          apply True.intro
                        let assump_132 := assump_125 assump_200
                        apply False.elim assump_132
          case inr assump_76 =>
            cases assump_3
            case inl assump_140 =>
              cases assump_140
              case intro assump_142 assump_143 =>
                cases assump_142
                case intro assump_144 assump_145 =>
                  have assump_201 : (p3 → True) := by
                    intro assump_153
                    apply True.intro
                  let assump_152 := assump_143 assump_201
                  apply False.elim assump_152
            case inr assump_141 =>
              cases assump_141
              case intro assump_157 assump_158 =>
                cases assump_157
                case intro assump_159 assump_160 =>
                  cases assump_159
                  case intro assump_161 assump_162 =>
                    cases assump_160
                    case inl assump_167 =>
                      cases assump_158
                      case intro assump_171 assump_172 =>
                        have assump_202 : True := by
                          apply True.intro
                        let assump_178 := assump_171 assump_202
                        apply False.elim assump_178
                    case inr assump_168 =>
                      cases assump_158
                      case intro assump_184 assump_185 =>
                        have assump_203 : True := by
                          apply True.intro
                        let assump_191 := assump_184 assump_203
                        apply False.elim assump_191


variable (p6 p0 p4 p5 p1 p3 p7 p2 : Prop)
theorem file37_30867 : (((((p5 → p4) ∧ (p7 ∨ p4)) → False) ∧ (((False ∧ p5) ∨ (True ∨ p1)) ∧ ((p6 → False) → False))) → ((((True ∧ p1) ∨ (p5 → p3)) ∧ ((p0 ∨ p4) ∨ (p5 ∧ p0))) → (((True ∨ p0) ∨ (True → p2)) ∨ ((False ∨ p0) → (p3 ∧ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_1
            case intro assump_19 assump_20 =>
              cases assump_20
              case intro assump_23 assump_24 =>
                cases assump_23
                case inl assump_25 =>
                  cases assump_25
                  case intro assump_27 assump_28 =>
                    apply False.elim assump_27
                case inr assump_26 =>
                  cases assump_26
                  case inl assump_31 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_32 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
          case inr assump_16 =>
            cases assump_1
            case intro assump_43 assump_44 =>
              cases assump_44
              case intro assump_47 assump_48 =>
                cases assump_47
                case inl assump_49 =>
                  cases assump_49
                  case intro assump_51 assump_52 =>
                    apply False.elim assump_51
                case inr assump_50 =>
                  cases assump_50
                  case inl assump_55 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_56 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
        case inr assump_14 =>
          cases assump_14
          case intro assump_65 assump_66 =>
            cases assump_1
            case intro assump_71 assump_72 =>
              cases assump_72
              case intro assump_75 assump_76 =>
                cases assump_75
                case inl assump_77 =>
                  cases assump_77
                  case intro assump_79 assump_80 =>
                    apply False.elim assump_79
                case inr assump_78 =>
                  cases assump_78
                  case inl assump_83 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_84 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
    case inr assump_6 =>
      cases assump_4
      case inl assump_95 =>
        cases assump_95
        case inl assump_97 =>
          cases assump_1
          case intro assump_101 assump_102 =>
            cases assump_102
            case intro assump_105 assump_106 =>
              cases assump_105
              case inl assump_107 =>
                cases assump_107
                case intro assump_109 assump_110 =>
                  apply False.elim assump_109
              case inr assump_108 =>
                cases assump_108
                case inl assump_113 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_114 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
        case inr assump_98 =>
          cases assump_1
          case intro assump_125 assump_126 =>
            cases assump_126
            case intro assump_129 assump_130 =>
              cases assump_129
              case inl assump_131 =>
                cases assump_131
                case intro assump_133 assump_134 =>
                  apply False.elim assump_133
              case inr assump_132 =>
                cases assump_132
                case inl assump_137 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_138 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
      case inr assump_96 =>
        cases assump_96
        case intro assump_147 assump_148 =>
          cases assump_1
          case intro assump_153 assump_154 =>
            cases assump_154
            case intro assump_157 assump_158 =>
              cases assump_157
              case inl assump_159 =>
                cases assump_159
                case intro assump_161 assump_162 =>
                  apply False.elim assump_161
              case inr assump_160 =>
                cases assump_160
                case inl assump_165 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_166 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro


variable (p6 p4 p0 p5 : Prop)
theorem file37_36414 : (((((p5 ∨ p5) ∨ (p5 → False)) → False) ∨ (((p6 → False) ∧ (p5 → False)) ∧ ((p5 ∧ False) ∧ (p4 ∨ p0)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_34 : ((p5 ∨ p5) ∨ (p5 → False)) := by
      apply Or.inr
      intro assump_7
      have assump_35 : ((p5 ∨ p5) ∨ (p5 → False)) := by
        apply Or.inl
        apply Or.inl
        exact assump_7
      let assump_11 := assump_2 assump_35
      apply False.elim assump_11
    let assump_6 := assump_2 assump_34
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_19
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_29


variable (p6 p4 p1 p0 p7 p3 p5 p2 : Prop)
theorem file37_37331 : ((((((False → False) ∨ (p5 → False)) → False) ∨ (((p7 → False) ∨ (p2 ∨ p5)) → ((True ∧ p6) ∧ (p4 → False)))) ∧ ((((p1 → p5) ∧ (p3 → True)) ∨ ((p0 ∧ p7) ∨ (p2 → False))) ∧ (((True → p1) → False) ∧ ((p0 ∧ False) ∧ (True ∨ p7))))) → False) := by
  intro assump_48
  cases assump_48
  case intro assump_49 assump_50 =>
    cases assump_49
    case inl assump_51 =>
      cases assump_50
      case intro assump_55 assump_56 =>
        cases assump_55
        case inl assump_57 =>
          cases assump_57
          case intro assump_59 assump_60 =>
            cases assump_56
            case intro assump_65 assump_66 =>
              cases assump_66
              case intro assump_69 assump_70 =>
                cases assump_69
                case intro assump_71 assump_72 =>
                  apply False.elim assump_72
        case inr assump_58 =>
          cases assump_58
          case inl assump_77 =>
            cases assump_77
            case intro assump_79 assump_80 =>
              cases assump_56
              case intro assump_85 assump_86 =>
                cases assump_86
                case intro assump_89 assump_90 =>
                  cases assump_89
                  case intro assump_91 assump_92 =>
                    apply False.elim assump_92
          case inr assump_78 =>
            cases assump_56
            case intro assump_99 assump_100 =>
              cases assump_100
              case intro assump_103 assump_104 =>
                cases assump_103
                case intro assump_105 assump_106 =>
                  apply False.elim assump_106
    case inr assump_52 =>
      cases assump_50
      case intro assump_113 assump_114 =>
        cases assump_113
        case inl assump_115 =>
          cases assump_115
          case intro assump_117 assump_118 =>
            cases assump_114
            case intro assump_123 assump_124 =>
              cases assump_124
              case intro assump_127 assump_128 =>
                cases assump_127
                case intro assump_129 assump_130 =>
                  apply False.elim assump_130
        case inr assump_116 =>
          cases assump_116
          case inl assump_135 =>
            cases assump_135
            case intro assump_137 assump_138 =>
              cases assump_114
              case intro assump_143 assump_144 =>
                cases assump_144
                case intro assump_147 assump_148 =>
                  cases assump_147
                  case intro assump_149 assump_150 =>
                    apply False.elim assump_150
          case inr assump_136 =>
            cases assump_114
            case intro assump_157 assump_158 =>
              cases assump_158
              case intro assump_161 assump_162 =>
                cases assump_161
                case intro assump_163 assump_164 =>
                  apply False.elim assump_164


variable (p2 p1 p5 p7 p6 p4 : Prop)
theorem file37_40292 : (((((False → p6) ∨ (True → p6)) → False) → (((p1 ∨ p4) → False) ∧ ((p5 ∨ p2) → False))) ∧ ((((False → False) → False) → ((p7 ∨ p1) ∨ (p6 → p2))) ∨ (((False → p5) → False) → False))) := by
  apply And.intro
  intro assump_7
  apply And.intro
  intro assump_8
  cases assump_8
  case inl assump_9 =>
    have assump_72 : ((False → p6) ∨ (True → p6)) := by
      apply Or.inl
      intro assump_16
      apply False.elim assump_16
    let assump_15 := assump_7 assump_72
    apply False.elim assump_15
  case inr assump_10 =>
    have assump_73 : ((False → p6) ∨ (True → p6)) := by
      apply Or.inl
      intro assump_27
      apply False.elim assump_27
    let assump_26 := assump_7 assump_73
    apply False.elim assump_26
  intro assump_33
  cases assump_33
  case inl assump_34 =>
    have assump_74 : ((False → p6) ∨ (True → p6)) := by
      apply Or.inl
      intro assump_41
      apply False.elim assump_41
    let assump_40 := assump_7 assump_74
    apply False.elim assump_40
  case inr assump_35 =>
    have assump_75 : ((False → p6) ∨ (True → p6)) := by
      apply Or.inl
      intro assump_52
      apply False.elim assump_52
    let assump_51 := assump_7 assump_75
    apply False.elim assump_51
  apply Or.inl
  intro assump_58
  apply Or.inr
  intro assump_61
  have assump_76 : (False → False) := by
    intro assump_66
    apply False.elim assump_66
  let assump_65 := assump_58 assump_76
  apply False.elim assump_65


variable (p7 p5 p2 p0 : Prop)
theorem file37_41782 : ((((((True ∧ False) ∧ (p0 → False)) ∧ ((p0 ∨ p7) ∨ (p5 ∧ p2))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((True ∧ False) ∧ (p0 → False)) ∧ ((p0 ∨ p7) ∨ (p5 ∧ p2))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p2 p7 p5 p4 p0 : Prop)
theorem file37_42350 : (((((p1 ∨ p4) ∨ (p5 ∧ False)) → ((p7 ∨ True) ∨ (p2 → p4))) → False) → ((((False → False) ∨ (p7 ∨ p5)) → ((True → p0) → False)) → False)) := by
  intro assump_1
  intro assump_2
  have assump_26 : (((p1 ∨ p4) ∨ (p5 ∧ False)) → ((p7 ∨ True) ∨ (p2 → p4))) := by
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_12 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
    case inr assump_10 =>
      cases assump_10
      case intro assump_17 assump_18 =>
        apply False.elim assump_18
  let assump_7 := assump_1 assump_26
  apply False.elim assump_7


variable (p6 p7 p2 p5 p1 p4 p3 p0 : Prop)
theorem file37_43137 : ((((((False ∨ p5) → False) → False) ∨ (((p4 → p2) → (False → False)) ∧ ((p6 ∧ p0) ∧ (p6 ∧ p5)))) ∧ ((((p3 → False) ∨ (p7 → False)) ∨ ((p7 ∨ False) → False)) ∧ (((p0 ∨ p1) ∧ (True → False)) ∧ ((p0 ∨ p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case inl assump_20 =>
                  have assump_209 : (p0 ∨ p2) := by
                    apply Or.inl
                    exact assump_20
                  let assump_28 := assump_17 assump_209
                  apply False.elim assump_28
                case inr assump_21 =>
                  have assump_210 : True := by
                    apply True.intro
                  let assump_39 := assump_19 assump_210
                  apply False.elim assump_39
          case inr assump_13 =>
            cases assump_9
            case intro assump_45 assump_46 =>
              cases assump_45
              case intro assump_47 assump_48 =>
                cases assump_47
                case inl assump_49 =>
                  have assump_211 : (p0 ∨ p2) := by
                    apply Or.inl
                    exact assump_49
                  let assump_57 := assump_46 assump_211
                  apply False.elim assump_57
                case inr assump_50 =>
                  have assump_212 : True := by
                    apply True.intro
                  let assump_68 := assump_48 assump_212
                  apply False.elim assump_68
        case inr assump_11 =>
          cases assump_9
          case intro assump_74 assump_75 =>
            cases assump_74
            case intro assump_76 assump_77 =>
              cases assump_76
              case inl assump_78 =>
                have assump_213 : (p0 ∨ p2) := by
                  apply Or.inl
                  exact assump_78
                let assump_86 := assump_75 assump_213
                apply False.elim assump_86
              case inr assump_79 =>
                have assump_214 : True := by
                  apply True.intro
                let assump_97 := assump_77 assump_214
                apply False.elim assump_97
    case inr assump_5 =>
      cases assump_5
      case intro assump_101 assump_102 =>
        cases assump_102
        case intro assump_105 assump_106 =>
          cases assump_105
          case intro assump_107 assump_108 =>
            cases assump_106
            case intro assump_113 assump_114 =>
              cases assump_3
              case intro assump_119 assump_120 =>
                cases assump_119
                case inl assump_121 =>
                  cases assump_121
                  case inl assump_123 =>
                    cases assump_120
                    case intro assump_127 assump_128 =>
                      cases assump_127
                      case intro assump_129 assump_130 =>
                        cases assump_129
                        case inl assump_131 =>
                          have assump_215 : (p0 ∨ p2) := by
                            apply Or.inl
                            exact assump_131
                          let assump_139 := assump_128 assump_215
                          apply False.elim assump_139
                        case inr assump_132 =>
                          have assump_216 : (p0 ∨ p2) := by
                            apply Or.inl
                            exact assump_108
                          let assump_149 := assump_128 assump_216
                          apply False.elim assump_149
                  case inr assump_124 =>
                    cases assump_120
                    case intro assump_155 assump_156 =>
                      cases assump_155
                      case intro assump_157 assump_158 =>
                        cases assump_157
                        case inl assump_159 =>
                          have assump_217 : (p0 ∨ p2) := by
                            apply Or.inl
                            exact assump_159
                          let assump_167 := assump_156 assump_217
                          apply False.elim assump_167
                        case inr assump_160 =>
                          have assump_218 : (p0 ∨ p2) := by
                            apply Or.inl
                            exact assump_108
                          let assump_177 := assump_156 assump_218
                          apply False.elim assump_177
                case inr assump_122 =>
                  cases assump_120
                  case intro assump_183 assump_184 =>
                    cases assump_183
                    case intro assump_185 assump_186 =>
                      cases assump_185
                      case inl assump_187 =>
                        have assump_219 : (p0 ∨ p2) := by
                          apply Or.inl
                          exact assump_187
                        let assump_195 := assump_184 assump_219
                        apply False.elim assump_195
                      case inr assump_188 =>
                        have assump_220 : (p0 ∨ p2) := by
                          apply Or.inl
                          exact assump_108
                        let assump_205 := assump_184 assump_220
                        apply False.elim assump_205


variable (p7 p0 p2 p4 p5 p3 p6 p1 : Prop)
theorem file37_48893 : (((((False ∧ p7) ∧ (p3 → p4)) ∧ ((p5 ∧ p0) → (p5 → False))) ∧ (((p0 ∧ p1) → False) ∨ ((p3 ∨ p7) → (p2 → True)))) → ((((p5 → False) ∨ (p3 ∨ p2)) ∧ ((p3 → False) ∧ (p6 → True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                apply False.elim assump_21
    case inr assump_6 =>
      cases assump_6
      case inl assump_25 =>
        cases assump_4
        case intro assump_29 assump_30 =>
          cases assump_1
          case intro assump_35 assump_36 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              cases assump_37
              case intro assump_39 assump_40 =>
                cases assump_39
                case intro assump_41 assump_42 =>
                  apply False.elim assump_41
      case inr assump_26 =>
        cases assump_4
        case intro assump_47 assump_48 =>
          cases assump_1
          case intro assump_53 assump_54 =>
            cases assump_53
            case intro assump_55 assump_56 =>
              cases assump_55
              case intro assump_57 assump_58 =>
                cases assump_57
                case intro assump_59 assump_60 =>
                  apply False.elim assump_59


variable (p2 p7 p4 p0 p3 p6 p5 : Prop)
theorem file37_50595 : (((((p5 → p5) ∨ (p5 → False)) ∧ ((p6 ∧ p4) ∨ (p3 → p5))) → (((p0 ∨ p5) ∧ (p2 ∧ p4)) → ((p0 → False) → (True → False)))) → ((((p0 ∧ p4) → False) ∧ ((p2 ∧ False) → False)) → (((False ∨ False) → False) ∨ ((p7 ∨ p7) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    intro assump_11
    cases assump_11
    case inl assump_12 =>
      apply False.elim assump_12
    case inr assump_13 =>
      apply False.elim assump_13


variable (p6 p3 p1 p5 p2 : Prop)
theorem file37_51142 : (((((p5 → False) → (p1 ∧ p5)) ∧ ((p6 → False) → (p6 → p2))) ∧ (((p2 ∨ False) → (p3 → p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_26 : ((p2 ∨ False) → (p3 → p2)) := by
        intro assump_13
        intro assump_14
        cases assump_13
        case inl assump_17 =>
          exact assump_17
        case inr assump_18 =>
          apply False.elim assump_18
      let assump_12 := assump_3 assump_26
      apply False.elim assump_12


variable (p2 p7 p1 p4 p6 : Prop)
theorem file37_51763 : (((((p2 ∨ p7) ∨ (True ∨ p4)) ∨ ((p4 ∨ p6) ∨ (p1 ∨ p2))) → False) → False) := by
  intro assump_22
  have assump_29 : (((p2 ∨ p7) ∨ (True ∨ p4)) ∨ ((p4 ∨ p6) ∨ (p1 ∨ p2))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_25 := assump_22 assump_29
  apply False.elim assump_25


variable (p7 p1 p5 p6 : Prop)
theorem file37_52134 : ((((((p1 ∧ p7) → False) ∧ ((False → False) → False)) → False) → ((((p5 → False) → False) → ((False ∧ p6) → False)) → False)) → False) := by
  intro assump_1
  have assump_29 : ((((p1 ∧ p7) → False) ∧ ((False → False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_30 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_30
      apply False.elim assump_12
  let assump_4 := assump_1 assump_29
  have assump_31 : (((p5 → False) → False) → ((False ∧ p6) → False)) := by
    intro assump_20
    intro assump_21
    cases assump_21
    case intro assump_22 assump_23 =>
      apply False.elim assump_22
  let assump_19 := assump_4 assump_31
  apply False.elim assump_19


variable (p2 p4 p5 : Prop)
theorem file37_52990 : (((((p2 ∧ p4) → (p5 ∨ True)) ∧ ((True → False) → (p5 → False))) → (((False → False) → (False → True)) → False)) → False) := by
  intro assump_33
  have assump_60 : (((p2 ∧ p4) → (p5 ∨ True)) ∧ ((True → False) → (p5 → False))) := by
    apply And.intro
    intro assump_37
    cases assump_37
    case intro assump_38 assump_39 =>
      apply Or.inr
      apply True.intro
    intro assump_44
    intro assump_45
    have assump_61 : True := by
      apply True.intro
    let assump_50 := assump_44 assump_61
    apply False.elim assump_50
  let assump_36 := assump_33 assump_60
  have assump_62 : ((False → False) → (False → True)) := by
    intro assump_55
    intro assump_56
    apply True.intro
  let assump_54 := assump_36 assump_62
  apply False.elim assump_54


variable (p1 p5 p3 p0 p6 p4 : Prop)
theorem file37_53817 : ((((((p1 → False) → False) → ((False → False) ∨ (p6 → False))) ∧ (((p0 → False) → False) → ((p6 → p4) → False))) ∧ ((((p6 → p3) → False) ∧ ((p0 ∨ p3) → False)) ∧ (((True ∨ p5) ∧ (p6 → p3)) ∧ ((False → p3) ∨ (p4 → p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_19
                case inl assump_28 =>
                  have assump_102 : (p6 → p3) := by
                    intro assump_36
                    have assump_103 : p6 := by
                      exact assump_36
                    let assump_41 := assump_21 assump_103
                    exact assump_41
                  let assump_35 := assump_12 assump_102
                  apply False.elim assump_35
                case inr assump_29 =>
                  have assump_104 : (p6 → p3) := by
                    intro assump_52
                    have assump_105 : p6 := by
                      exact assump_52
                    let assump_57 := assump_21 assump_105
                    exact assump_57
                  let assump_51 := assump_12 assump_104
                  apply False.elim assump_51
              case inr assump_23 =>
                cases assump_19
                case inl assump_66 =>
                  have assump_106 : (p6 → p3) := by
                    intro assump_75
                    have assump_107 : p6 := by
                      exact assump_75
                    let assump_80 := assump_21 assump_107
                    exact assump_80
                  let assump_74 := assump_12 assump_106
                  apply False.elim assump_74
                case inr assump_67 =>
                  have assump_108 : (p6 → p3) := by
                    intro assump_92
                    have assump_109 : p6 := by
                      exact assump_92
                    let assump_97 := assump_21 assump_109
                    exact assump_97
                  let assump_91 := assump_12 assump_108
                  apply False.elim assump_91


variable (p0 p3 p2 p6 p4 p5 : Prop)
theorem file37_56297 : ((((((p3 ∧ p5) ∧ (p3 → p4)) → ((p2 ∧ False) → False)) ∨ (((True → False) ∧ (p6 ∨ p4)) ∨ ((p0 → p0) → False))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p3 ∧ p5) ∧ (p3 → p4)) → ((p2 ∧ False) → False)) ∨ (((True → False) ∧ (p6 ∨ p4)) ∨ ((p0 → p0) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p1 p2 p5 p7 p3 p6 p0 : Prop)
theorem file37_56851 : (((((False → False) ∧ (p7 ∧ False)) ∨ ((True → p2) → (p1 → p1))) ∧ (((False ∧ p6) → (False ∧ True)) ∨ ((p3 → True) ∨ (True ∨ p2)))) ∨ ((((False ∧ False) → False) → ((True → False) ∧ (p0 → False))) → (((p3 ∧ p1) ∧ (p5 → p2)) ∧ ((p5 → False) ∧ (p1 ∨ p7))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inr
  intro assump_4
  intro assump_5
  exact assump_5
  apply Or.inl
  intro assump_10
  apply And.intro
  cases assump_10
  case intro assump_11 assump_12 =>
    apply False.elim assump_11
  apply True.intro


variable (p2 p7 p0 p3 p4 p5 p6 : Prop)
theorem file37_57430 : (((((p4 → False) → (p3 → p4)) ∨ ((p5 → False) ∧ (p7 ∧ p7))) → False) → ((((p2 → False) ∧ (p6 → p6)) ∧ ((p0 → False) ∧ (p4 ∨ False))) → (((p3 → False) → False) ∧ ((p3 ∨ p0) → (p2 → p5))))) := by
  intro assump_15
  intro assump_16
  apply And.intro
  intro assump_17
  cases assump_16
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_21
      case intro assump_28 assump_29 =>
        cases assump_29
        case inl assump_32 =>
          have assump_120 : (((p4 → False) → (p3 → p4)) ∨ ((p5 → False) ∧ (p7 ∧ p7))) := by
            apply Or.inl
            intro assump_39
            intro assump_40
            exact assump_32
          let assump_38 := assump_15 assump_120
          apply False.elim assump_38
        case inr assump_33 =>
          apply False.elim assump_33
  intro assump_50
  intro assump_51
  cases assump_50
  case inl assump_54 =>
    cases assump_16
    case intro assump_58 assump_59 =>
      cases assump_58
      case intro assump_60 assump_61 =>
        cases assump_59
        case intro assump_66 assump_67 =>
          cases assump_67
          case inl assump_70 =>
            have assump_121 : (((p4 → False) → (p3 → p4)) ∨ ((p5 → False) ∧ (p7 ∧ p7))) := by
              apply Or.inl
              intro assump_77
              intro assump_78
              exact assump_70
            let assump_76 := assump_15 assump_121
            apply False.elim assump_76
          case inr assump_71 =>
            apply False.elim assump_71
  case inr assump_55 =>
    cases assump_16
    case intro assump_90 assump_91 =>
      cases assump_90
      case intro assump_92 assump_93 =>
        cases assump_91
        case intro assump_98 assump_99 =>
          cases assump_99
          case inl assump_102 =>
            have assump_122 : (((p4 → False) → (p3 → p4)) ∨ ((p5 → False) ∧ (p7 ∧ p7))) := by
              apply Or.inl
              intro assump_109
              intro assump_110
              exact assump_102
            let assump_108 := assump_15 assump_122
            apply False.elim assump_108
          case inr assump_103 =>
            apply False.elim assump_103


variable (p3 p1 p2 p5 p7 p6 : Prop)
theorem file37_59677 : (((((p1 ∧ p6) ∨ (False ∨ p2)) ∧ ((False → p6) → (p3 ∨ p2))) → False) → ((((False → p6) ∧ (p2 ∧ p2)) → ((p6 ∨ False) ∧ (p2 → p1))) ∨ (((p5 → False) → False) ∧ ((p7 → p5) → (True ∨ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_49 : (((p1 ∧ p6) ∨ (False ∨ p2)) ∧ ((False → p6) → (p3 ∨ p2))) := by
        apply And.intro
        apply Or.inr
        apply Or.inr
        exact assump_10
        intro assump_19
        apply Or.inr
        exact assump_10
      let assump_18 := assump_1 assump_49
      apply False.elim assump_18
  intro assump_25
  cases assump_4
  case intro assump_28 assump_29 =>
    cases assump_29
    case intro assump_32 assump_33 =>
      have assump_50 : (((p1 ∧ p6) ∨ (False ∨ p2)) ∧ ((False → p6) → (p3 ∨ p2))) := by
        apply And.intro
        apply Or.inr
        apply Or.inr
        exact assump_33
        intro assump_43
        apply Or.inr
        exact assump_33
      let assump_42 := assump_1 assump_50
      apply False.elim assump_42


variable (p4 p3 p5 p2 p1 p0 p6 : Prop)
theorem file37_60881 : ((((((p5 → False) → False) ∨ ((p0 ∨ p2) → (p5 → p3))) → False) ∧ ((((p5 ∧ p6) ∧ (p5 ∨ p5)) ∧ ((p1 ∧ False) ∧ (p2 ∧ p5))) ∧ (((p6 ∨ p4) ∨ (p1 → p2)) → ((p5 → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_11
            case inl assump_18 =>
              cases assump_9
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
            case inr assump_19 =>
              cases assump_9
              case intro assump_32 assump_33 =>
                cases assump_32
                case intro assump_34 assump_35 =>
                  apply False.elim assump_35


variable (p4 p6 p0 p1 p5 p7 : Prop)
theorem file37_61953 : ((((((True → p5) ∧ (p6 ∨ False)) → ((p6 ∨ True) → (True ∨ p6))) ∨ (((p4 → False) → (p0 → p1)) ∧ ((p7 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_36 : ((((True → p5) ∧ (p6 ∨ False)) → ((p6 ∨ True) → (True ∨ p6))) ∨ (((p4 → False) → (p0 → p1)) ∧ ((p7 → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          apply Or.inl
          apply True.intro
        case inr assump_16 =>
          apply False.elim assump_16
    case inr assump_8 =>
      cases assump_5
      case intro assump_23 assump_24 =>
        cases assump_24
        case inl assump_27 =>
          apply Or.inl
          apply True.intro
        case inr assump_28 =>
          apply False.elim assump_28
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p2 p5 p0 p6 : Prop)
theorem file37_62966 : ((((((False → p0) ∨ (p2 ∨ p5)) ∧ ((p6 ∧ False) ∧ (False ∧ True))) → False) → False) → False) := by
  intro assump_1
  have assump_45 : ((((False → p0) ∨ (p2 ∨ p5)) ∧ ((p6 ∧ False) ∧ (False ∧ True))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
      case inr assump_9 =>
        cases assump_9
        case inl assump_20 =>
          cases assump_7
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              apply False.elim assump_27
        case inr assump_21 =>
          cases assump_7
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              apply False.elim assump_37
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


variable (p5 p2 p1 p7 p0 p6 p4 : Prop)
theorem file37_64082 : ((((((p6 ∨ p5) → (p1 → True)) → ((p2 ∧ p5) → False)) ∧ (((p5 → False) → False) ∧ ((False ∧ p6) ∧ (False ∧ False)))) ∧ ((((p0 → p6) ∧ (p4 ∨ p7)) → ((True ∧ p2) ∧ (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14


variable (p6 p5 p1 p4 p0 p2 p3 : Prop)
theorem file37_64702 : (((((p6 → False) ∧ (p0 ∨ False)) ∧ ((p4 ∧ p5) → (p5 ∧ p6))) ∨ (((p1 → p3) → False) ∨ ((p0 ∧ p5) → False))) → ((((True → False) ∧ (p3 → False)) ∧ ((True ∨ p5) ∨ (p2 → False))) → (((True → False) ∧ (True → p6)) → ((True ∨ p2) ∨ (p0 → p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case inl assump_18 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_1
            case inl assump_24 =>
              cases assump_24
              case intro assump_26 assump_27 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  cases assump_29
                  case inl assump_32 =>
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_33 =>
                    apply False.elim assump_33
            case inr assump_25 =>
              cases assump_25
              case inl assump_40 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_41 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_21 =>
            cases assump_1
            case inl assump_48 =>
              cases assump_48
              case intro assump_50 assump_51 =>
                cases assump_50
                case intro assump_52 assump_53 =>
                  cases assump_53
                  case inl assump_56 =>
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_57 =>
                    apply False.elim assump_57
            case inr assump_49 =>
              cases assump_49
              case inl assump_64 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_65 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
        case inr assump_19 =>
          cases assump_1
          case inl assump_72 =>
            cases assump_72
            case intro assump_74 assump_75 =>
              cases assump_74
              case intro assump_76 assump_77 =>
                cases assump_77
                case inl assump_80 =>
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_81 =>
                  apply False.elim assump_81
          case inr assump_73 =>
            cases assump_73
            case inl assump_88 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_89 =>
              apply Or.inl
              apply Or.inl
              apply True.intro


variable (p3 p6 p7 p5 p0 : Prop)
theorem file37_67763 : (((((p7 → True) ∧ (False ∧ True)) ∧ ((p0 ∨ p6) ∨ (p7 ∧ p0))) ∧ (((p3 → False) ∨ (p5 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p3 p2 p4 p6 p7 : Prop)
theorem file37_68223 : ((((((p4 → p4) ∨ (p7 → False)) ∨ ((p2 → p3) ∨ (False ∧ False))) ∨ (((True ∨ False) ∧ (p7 → False)) → ((True → False) ∧ (p6 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p4 → p4) ∨ (p7 → False)) ∨ ((p2 → p3) ∨ (False ∧ False))) ∨ (((True ∨ False) ∧ (p7 → False)) → ((True → False) ∧ (p6 ∨ p6)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p6 p5 p2 p4 p3 : Prop)
theorem file37_68765 : (((((p2 → True) → False) ∨ ((p2 → False) → (p5 → False))) → (((p4 ∧ False) → False) ∨ ((p3 → True) ∨ (True → p2)))) ∨ ((((p3 → p3) ∨ (p0 ∧ False)) ∧ ((p6 → False) → (p3 ∧ p4))) ∨ (((p5 → False) → (p4 → p3)) ∨ ((p6 → False) ∧ (False ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  case inr assump_3 =>
    apply Or.inl
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      apply False.elim assump_17


variable (p2 p3 p1 p6 : Prop)
theorem file37_69413 : ((((((p6 → False) → False) → False) → (((p3 → p3) ∨ (p2 → False)) ∨ ((p1 ∧ p2) → (p1 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p6 → False) → False) → False) → (((p3 → p3) ∨ (p2 → False)) ∨ ((p1 ∧ p2) → (p1 ∧ False)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p6 p5 p1 : Prop)
theorem file37_69881 : (((((False ∧ p1) → (p2 → p5)) ∨ ((p6 → False) ∨ (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_16 : (((False ∧ p1) → (p2 → p5)) ∨ ((p6 → False) ∨ (p6 → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p2 p5 p3 p4 p0 p1 : Prop)
theorem file37_70342 : ((((((True → p1) → False) ∨ ((p0 → False) → (p0 → False))) → False) ∧ ((((p1 ∧ p2) ∧ (p0 ∧ p3)) → ((p1 ∨ p7) ∨ (p0 ∨ p4))) → (((p0 → False) ∧ (p5 ∧ True)) ∧ ((True ∨ False) → (False ∨ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_38 : (((p1 ∧ p2) ∧ (p0 ∧ p3)) → ((p1 ∨ p7) ∨ (p0 ∨ p4))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply Or.inl
            apply Or.inl
            exact assump_12
    let assump_8 := assump_3 assump_38
    let assump_24 := And.right assump_8
    have assump_39 : (True ∨ False) := by
      apply Or.inl
      apply True.intro
    let assump_30 := assump_24 assump_39
    cases assump_30
    case inl assump_32 =>
      apply False.elim assump_32
    case inr assump_33 =>
      apply False.elim assump_33


variable (p5 p6 p0 p1 p3 p2 p7 p4 : Prop)
theorem file37_71403 : (((((p1 ∧ p5) ∨ (p7 ∨ p6)) → ((p2 → False) → (p2 → False))) ∨ (((p6 → False) ∧ (p4 → False)) ∨ ((p3 ∨ p1) ∨ (p6 ∧ p0)))) ∨ ((((p5 → p0) ∧ (p5 → False)) → ((True ∨ p6) → (True → False))) → (((p0 ∨ p5) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_30
  intro assump_31
  intro assump_32
  cases assump_30
  case inl assump_37 =>
    cases assump_37
    case intro assump_39 assump_40 =>
      have assump_67 : p2 := by
        exact assump_32
      let assump_47 := assump_31 assump_67
      apply False.elim assump_47
  case inr assump_38 =>
    cases assump_38
    case inl assump_51 =>
      have assump_68 : p2 := by
        exact assump_32
      let assump_56 := assump_31 assump_68
      apply False.elim assump_56
    case inr assump_52 =>
      have assump_69 : p2 := by
        exact assump_32
      let assump_63 := assump_31 assump_69
      apply False.elim assump_63


variable (p0 p6 p3 p7 p2 p5 p1 p4 : Prop)
theorem file37_72371 : ((((((True ∧ p1) → (p2 → p5)) ∧ ((True ∧ p7) → False)) → (((p5 ∨ p2) ∧ (p0 → False)) → False)) ∧ ((((p6 ∨ p0) → (p7 → p7)) → ((False ∧ p4) ∨ (p6 ∨ p3))) ∧ (((True ∨ p3) ∨ (p6 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_16 : ((True ∨ p3) ∨ (p6 → False)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_12 := assump_7 assump_16
      apply False.elim assump_12


variable (p0 p7 p6 p1 p3 p5 p4 : Prop)
theorem file37_72968 : (((((False ∨ p4) → (p3 ∧ p4)) → ((p0 ∨ p5) ∨ (p6 ∧ p1))) → (((p1 ∧ False) ∨ (p6 ∧ p3)) ∨ ((False ∧ p4) → (p0 → p0)))) ∨ ((((p3 ∨ True) ∨ (p6 → p7)) ∧ ((p4 ∧ p3) → False)) → False)) := by
  apply Or.inl
  intro assump_49
  apply Or.inr
  intro assump_52
  intro assump_53
  cases assump_52
  case intro assump_56 assump_57 =>
    apply False.elim assump_56


variable (p3 p6 p2 p4 p1 p5 : Prop)
theorem file37_73384 : ((((((p2 ∧ p2) ∨ (p3 → False)) → ((p6 ∨ True) → (p5 → True))) ∨ (((p1 → p4) ∨ (p2 → False)) ∧ ((True ∨ True) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p2 ∧ p2) ∨ (p3 → False)) → ((p6 ∨ True) → (p5 → True))) ∨ (((p1 → p4) ∨ (p2 → False)) ∧ ((True ∨ True) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p3 p0 p1 p7 p2 p4 p6 : Prop)
theorem file37_73914 : (((((p3 → p7) → False) → False) → (((p3 ∨ p7) → (p4 → True)) ∨ ((p6 → True) ∨ (False ∧ p1)))) ∨ ((((p2 → True) → False) → ((p5 → False) → False)) ∨ (((p0 → False) → False) ∨ ((False → False) ∨ (p2 ∨ True))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p3 p1 p2 p0 p7 : Prop)
theorem file37_74286 : (((((p2 → p2) → False) → False) ∨ (((p1 ∧ p2) → (p2 → p1)) → False)) ∨ ((((p2 → p3) ∨ (p2 ∨ False)) → False) ∧ (((True → True) → (p7 → p7)) ∧ ((p0 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (p2 → p2) := by
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p5 p3 p1 p6 p2 : Prop)
theorem file37_74705 : (((((p0 → p0) → False) → False) ∨ (((p5 ∨ p3) → False) → ((True → True) → (False ∧ p1)))) ∨ ((((p6 → p6) ∨ (True ∨ p1)) → ((p6 ∨ p5) → (p2 → True))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (p0 → p0) := by
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p2 p0 p6 p4 p1 p7 p5 : Prop)
theorem file37_75121 : ((((((p5 → False) ∨ (p4 → False)) → ((p2 → False) → False)) ∧ (((p3 ∧ False) → (False ∧ p6)) → False)) ∧ ((((p5 ∨ p1) ∨ (p0 ∨ p0)) → ((p0 ∧ False) ∧ (p5 ∨ p1))) ∨ (((p3 ∧ p2) → (p2 → p6)) ∧ ((p7 → p4) ∨ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        have assump_80 : ((p3 ∧ False) → (False ∧ p6)) := by
          intro assump_16
          apply And.intro
          cases assump_16
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
          cases assump_16
          case intro assump_23 assump_24 =>
            apply False.elim assump_24
        let assump_15 := assump_5 assump_80
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case intro assump_32 assump_33 =>
          cases assump_33
          case inl assump_36 =>
            have assump_81 : ((p3 ∧ False) → (False ∧ p6)) := by
              intro assump_43
              apply And.intro
              cases assump_43
              case intro assump_44 assump_45 =>
                apply False.elim assump_45
              cases assump_43
              case intro assump_50 assump_51 =>
                apply False.elim assump_51
            let assump_42 := assump_5 assump_81
            apply False.elim assump_42
          case inr assump_37 =>
            have assump_82 : ((p3 ∧ False) → (False ∧ p6)) := by
              intro assump_64
              apply And.intro
              cases assump_64
              case intro assump_65 assump_66 =>
                apply False.elim assump_66
              cases assump_64
              case intro assump_71 assump_72 =>
                apply False.elim assump_72
            let assump_63 := assump_5 assump_82
            apply False.elim assump_63


variable (p2 p0 p6 p7 p1 p4 p3 : Prop)
theorem file37_77093 : (((((p2 ∧ p3) ∧ (False → p6)) → ((p3 → False) → False)) ∨ (((p6 ∧ p0) ∨ (p7 → False)) ∧ ((p4 ∨ p4) ∧ (p1 → True)))) ∨ ((((p0 → False) → False) → False) ∨ (((p7 → False) → (p6 ∨ p1)) → ((p1 ∨ p1) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_22 : p3 := by
        exact assump_8
      let assump_18 := assump_2 assump_22
      apply False.elim assump_18


variable (p6 p0 p2 p1 p5 p4 p3 p7 : Prop)
theorem file37_77672 : (((((p7 ∨ True) ∧ (False → False)) → ((p5 ∧ p1) → (p4 → p4))) ∨ (((True → False) → (False ∧ True)) ∨ ((True → False) ∧ (True → p2)))) ∨ ((((p3 → p6) → (p1 → False)) → False) → (((p0 → p1) → False) ∨ ((p3 → False) ∧ (p2 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_9
  intro assump_10
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    cases assump_9
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        exact assump_11
      case inr assump_23 =>
        exact assump_11


variable (p1 p0 p2 p6 p4 p5 : Prop)
theorem file37_78287 : ((((((p2 ∨ True) → False) → ((p0 → False) ∧ (p6 → False))) ∧ (((False ∧ p5) ∨ (False ∧ p2)) → ((p5 ∧ p1) → (p6 → False)))) ∧ ((((p1 → False) ∧ (False ∧ p6)) → False) ∧ (((p4 ∨ p6) ∨ (False → p1)) → False))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_11
      case intro assump_18 assump_19 =>
        have assump_31 : ((p4 ∨ p6) ∨ (False → p1)) := by
          apply Or.inr
          intro assump_25
          apply False.elim assump_25
        let assump_24 := assump_19 assump_31
        apply False.elim assump_24


variable (p5 p2 p7 p4 p6 : Prop)
theorem file37_78980 : ((((((p5 ∨ p2) → False) ∨ ((False → False) → False)) → (((True ∨ p5) ∨ (p6 ∧ True)) ∨ ((p7 ∨ p4) → (False → p2)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p5 ∨ p2) → False) ∨ ((False → False) → False)) → (((True ∨ p5) ∨ (p6 ∧ True)) ∨ ((p7 ∨ p4) → (False → p2)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p2 p0 p7 p4 p3 : Prop)
theorem file37_79647 : (((((False ∧ p3) ∧ (p3 ∧ p7)) → ((p7 ∧ p7) ∨ (p2 → False))) → False) → ((((p0 → p2) → False) ∨ ((p1 → False) ∨ (p4 ∧ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_56 : (((False ∧ p3) ∧ (p3 ∧ p7)) → ((p7 ∧ p7) ∨ (p2 → False))) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
    let assump_9 := assump_1 assump_56
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case inl assump_20 =>
      have assump_57 : (((False ∧ p3) ∧ (p3 ∧ p7)) → ((p7 ∧ p7) ∨ (p2 → False))) := by
        intro assump_27
        cases assump_27
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            apply False.elim assump_30
      let assump_26 := assump_1 assump_57
      apply False.elim assump_26
    case inr assump_21 =>
      cases assump_21
      case intro assump_37 assump_38 =>
        have assump_58 : (((False ∧ p3) ∧ (p3 ∧ p7)) → ((p7 ∧ p7) ∨ (p2 → False))) := by
          intro assump_46
          cases assump_46
          case intro assump_47 assump_48 =>
            cases assump_47
            case intro assump_49 assump_50 =>
              apply False.elim assump_49
        let assump_45 := assump_1 assump_58
        apply False.elim assump_45


variable (p1 p4 p3 p5 p6 p2 p0 p7 : Prop)
theorem file37_81163 : (((((p5 → p0) ∨ (p4 → False)) → ((p3 ∨ p5) → (p1 → False))) → False) → ((((True ∧ False) → (p6 → p0)) ∨ ((p5 ∨ p6) ∧ (p7 → p2))) ∨ (((p0 → p3) ∧ (p6 ∧ p5)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_9


variable (p7 p4 p5 p0 p2 p1 p6 : Prop)
theorem file37_81561 : ((((((p1 ∧ p1) ∧ (False ∧ False)) → False) ∨ (((p4 → False) → (p7 → False)) ∨ ((True ∧ p1) ∨ (p2 ∨ p1)))) → ((((True ∨ p7) ∨ (p0 ∨ True)) → False) ∧ (((p7 ∨ p1) ∧ (p5 → p5)) ∧ ((p6 → False) ∨ (True → False))))) → False) := by
  intro assump_1
  have assump_23 : ((((p1 ∧ p1) ∧ (False ∧ False)) → False) ∨ (((p4 → False) → (p7 → False)) ∨ ((True ∧ p1) ∨ (p2 ∨ p1)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
  let assump_4 := assump_1 assump_23
  let assump_18 := And.left assump_4
  have assump_24 : ((True ∨ p7) ∨ (p0 ∨ True)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_19 := assump_18 assump_24
  apply False.elim assump_19


variable (p0 p1 p2 p6 p5 p3 p7 p4 : Prop)
theorem file37_82501 : (((((p4 ∨ p4) ∧ (p1 ∨ p7)) → False) → (((False → p5) ∨ (p6 ∨ True)) ∨ ((p0 → False) → False))) ∨ ((((p7 → False) ∧ (False → False)) ∨ ((p2 ∧ p3) ∨ (p3 ∧ p6))) → (((p5 → p0) ∧ (p3 → False)) ∨ ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p2 p4 p0 p7 p6 p3 p1 : Prop)
theorem file37_82894 : (((((p3 ∧ p3) ∨ (p1 ∧ p1)) → ((p4 → False) → False)) → False) → ((((False ∧ p2) → False) ∧ ((False → True) ∨ (p6 → p0))) ∨ (((p2 ∧ p4) ∨ (p2 ∨ p7)) ∨ ((p7 ∧ p0) → False)))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5
  apply Or.inl
  intro assump_9
  apply True.intro


variable (p0 p6 p3 p1 p4 p7 : Prop)
theorem file37_83332 : ((((((False → False) → False) ∨ ((p6 → p4) ∨ (p1 ∨ p4))) → False) ∧ ((((p7 → p3) ∧ (p0 → False)) → ((p3 → False) → (False → p3))) ∧ (((True ∨ p4) → False) ∧ ((False → False) ∨ (p0 ∨ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          have assump_39 : (True ∨ p4) := by
            apply Or.inl
            apply True.intro
          let assump_19 := assump_10 assump_39
          apply False.elim assump_19
        case inr assump_15 =>
          cases assump_15
          case inl assump_23 =>
            have assump_40 : (True ∨ p4) := by
              apply Or.inl
              apply True.intro
            let assump_28 := assump_10 assump_40
            apply False.elim assump_28
          case inr assump_24 =>
            have assump_41 : (True ∨ p4) := by
              apply Or.inl
              apply True.intro
            let assump_35 := assump_10 assump_41
            apply False.elim assump_35


variable (p7 p4 p0 p1 p5 p2 p3 : Prop)
theorem file37_84527 : (((((False ∧ True) ∨ (p2 ∧ p5)) → False) ∧ (((False ∨ p3) ∨ (p5 → False)) → ((p2 → p1) ∧ (p1 → False)))) → ((((p4 ∧ True) ∨ (p0 ∧ p1)) ∧ ((p1 ∧ p3) ∧ (p5 → False))) → (((p1 → p4) ∨ (p1 ∨ p2)) → ((p7 ∧ p5) ∧ (False ∨ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply And.intro
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_9
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_1
              case intro assump_28 assump_29 =>
                have assump_576 : ((False ∨ p3) ∨ (p5 → False)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_21
                let assump_34 := assump_29 assump_576
                let assump_35 := And.right assump_34
                have assump_577 : p1 := by
                  exact assump_20
                let assump_37 := assump_35 assump_577
                apply False.elim assump_37
      case inr assump_11 =>
        cases assump_11
        case intro assump_41 assump_42 =>
          cases assump_9
          case intro assump_47 assump_48 =>
            cases assump_47
            case intro assump_49 assump_50 =>
              cases assump_1
              case intro assump_57 assump_58 =>
                have assump_578 : ((False ∨ p3) ∨ (p5 → False)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_50
                let assump_63 := assump_58 assump_578
                let assump_64 := And.right assump_63
                have assump_579 : p1 := by
                  exact assump_49
                let assump_66 := assump_64 assump_579
                apply False.elim assump_66
  case inr assump_5 =>
    cases assump_5
    case inl assump_70 =>
      cases assump_2
      case intro assump_74 assump_75 =>
        cases assump_74
        case inl assump_76 =>
          cases assump_76
          case intro assump_78 assump_79 =>
            cases assump_75
            case intro assump_84 assump_85 =>
              cases assump_84
              case intro assump_86 assump_87 =>
                cases assump_1
                case intro assump_94 assump_95 =>
                  have assump_580 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_87
                  let assump_100 := assump_95 assump_580
                  let assump_101 := And.right assump_100
                  have assump_581 : p1 := by
                    exact assump_86
                  let assump_103 := assump_101 assump_581
                  apply False.elim assump_103
        case inr assump_77 =>
          cases assump_77
          case intro assump_107 assump_108 =>
            cases assump_75
            case intro assump_113 assump_114 =>
              cases assump_113
              case intro assump_115 assump_116 =>
                cases assump_1
                case intro assump_123 assump_124 =>
                  have assump_582 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_116
                  let assump_129 := assump_124 assump_582
                  let assump_130 := And.right assump_129
                  have assump_583 : p1 := by
                    exact assump_115
                  let assump_132 := assump_130 assump_583
                  apply False.elim assump_132
    case inr assump_71 =>
      cases assump_2
      case intro assump_138 assump_139 =>
        cases assump_138
        case inl assump_140 =>
          cases assump_140
          case intro assump_142 assump_143 =>
            cases assump_139
            case intro assump_148 assump_149 =>
              cases assump_148
              case intro assump_150 assump_151 =>
                cases assump_1
                case intro assump_158 assump_159 =>
                  have assump_584 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_151
                  let assump_164 := assump_159 assump_584
                  let assump_165 := And.right assump_164
                  have assump_585 : p1 := by
                    exact assump_150
                  let assump_168 := assump_165 assump_585
                  apply False.elim assump_168
        case inr assump_141 =>
          cases assump_141
          case intro assump_172 assump_173 =>
            cases assump_139
            case intro assump_178 assump_179 =>
              cases assump_178
              case intro assump_180 assump_181 =>
                cases assump_1
                case intro assump_188 assump_189 =>
                  have assump_586 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_181
                  let assump_194 := assump_189 assump_586
                  let assump_195 := And.right assump_194
                  have assump_587 : p1 := by
                    exact assump_180
                  let assump_198 := assump_195 assump_587
                  apply False.elim assump_198
  cases assump_3
  case inl assump_202 =>
    cases assump_2
    case intro assump_206 assump_207 =>
      cases assump_206
      case inl assump_208 =>
        cases assump_208
        case intro assump_210 assump_211 =>
          cases assump_207
          case intro assump_216 assump_217 =>
            cases assump_216
            case intro assump_218 assump_219 =>
              cases assump_1
              case intro assump_226 assump_227 =>
                have assump_588 : ((False ∨ p3) ∨ (p5 → False)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_219
                let assump_232 := assump_227 assump_588
                let assump_233 := And.right assump_232
                have assump_589 : p1 := by
                  exact assump_218
                let assump_235 := assump_233 assump_589
                apply False.elim assump_235
      case inr assump_209 =>
        cases assump_209
        case intro assump_239 assump_240 =>
          cases assump_207
          case intro assump_245 assump_246 =>
            cases assump_245
            case intro assump_247 assump_248 =>
              cases assump_1
              case intro assump_255 assump_256 =>
                have assump_590 : ((False ∨ p3) ∨ (p5 → False)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_248
                let assump_261 := assump_256 assump_590
                let assump_262 := And.right assump_261
                have assump_591 : p1 := by
                  exact assump_247
                let assump_264 := assump_262 assump_591
                apply False.elim assump_264
  case inr assump_203 =>
    cases assump_203
    case inl assump_268 =>
      cases assump_2
      case intro assump_272 assump_273 =>
        cases assump_272
        case inl assump_274 =>
          cases assump_274
          case intro assump_276 assump_277 =>
            cases assump_273
            case intro assump_282 assump_283 =>
              cases assump_282
              case intro assump_284 assump_285 =>
                cases assump_1
                case intro assump_292 assump_293 =>
                  have assump_592 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_285
                  let assump_298 := assump_293 assump_592
                  let assump_299 := And.right assump_298
                  have assump_593 : p1 := by
                    exact assump_284
                  let assump_301 := assump_299 assump_593
                  apply False.elim assump_301
        case inr assump_275 =>
          cases assump_275
          case intro assump_305 assump_306 =>
            cases assump_273
            case intro assump_311 assump_312 =>
              cases assump_311
              case intro assump_313 assump_314 =>
                cases assump_1
                case intro assump_321 assump_322 =>
                  have assump_594 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_314
                  let assump_327 := assump_322 assump_594
                  let assump_328 := And.right assump_327
                  have assump_595 : p1 := by
                    exact assump_313
                  let assump_330 := assump_328 assump_595
                  apply False.elim assump_330
    case inr assump_269 =>
      cases assump_2
      case intro assump_336 assump_337 =>
        cases assump_336
        case inl assump_338 =>
          cases assump_338
          case intro assump_340 assump_341 =>
            cases assump_337
            case intro assump_346 assump_347 =>
              cases assump_346
              case intro assump_348 assump_349 =>
                cases assump_1
                case intro assump_356 assump_357 =>
                  have assump_596 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_349
                  let assump_362 := assump_357 assump_596
                  let assump_363 := And.right assump_362
                  have assump_597 : p1 := by
                    exact assump_348
                  let assump_366 := assump_363 assump_597
                  apply False.elim assump_366
        case inr assump_339 =>
          cases assump_339
          case intro assump_370 assump_371 =>
            cases assump_337
            case intro assump_376 assump_377 =>
              cases assump_376
              case intro assump_378 assump_379 =>
                cases assump_1
                case intro assump_386 assump_387 =>
                  have assump_598 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_379
                  let assump_392 := assump_387 assump_598
                  let assump_393 := And.right assump_392
                  have assump_599 : p1 := by
                    exact assump_378
                  let assump_396 := assump_393 assump_599
                  apply False.elim assump_396
  cases assump_3
  case inl assump_400 =>
    cases assump_2
    case intro assump_404 assump_405 =>
      cases assump_404
      case inl assump_406 =>
        cases assump_406
        case intro assump_408 assump_409 =>
          cases assump_405
          case intro assump_414 assump_415 =>
            cases assump_414
            case intro assump_416 assump_417 =>
              cases assump_1
              case intro assump_424 assump_425 =>
                apply Or.inr
                exact assump_408
      case inr assump_407 =>
        cases assump_407
        case intro assump_430 assump_431 =>
          cases assump_405
          case intro assump_436 assump_437 =>
            cases assump_436
            case intro assump_438 assump_439 =>
              cases assump_1
              case intro assump_446 assump_447 =>
                have assump_600 : ((False ∨ p3) ∨ (p5 → False)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_439
                let assump_452 := assump_447 assump_600
                let assump_453 := And.right assump_452
                have assump_601 : p1 := by
                  exact assump_438
                let assump_455 := assump_453 assump_601
                apply False.elim assump_455
  case inr assump_401 =>
    cases assump_401
    case inl assump_459 =>
      cases assump_2
      case intro assump_463 assump_464 =>
        cases assump_463
        case inl assump_465 =>
          cases assump_465
          case intro assump_467 assump_468 =>
            cases assump_464
            case intro assump_473 assump_474 =>
              cases assump_473
              case intro assump_475 assump_476 =>
                cases assump_1
                case intro assump_483 assump_484 =>
                  apply Or.inr
                  exact assump_467
        case inr assump_466 =>
          cases assump_466
          case intro assump_489 assump_490 =>
            cases assump_464
            case intro assump_495 assump_496 =>
              cases assump_495
              case intro assump_497 assump_498 =>
                cases assump_1
                case intro assump_505 assump_506 =>
                  have assump_602 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_498
                  let assump_511 := assump_506 assump_602
                  let assump_512 := And.right assump_511
                  have assump_603 : p1 := by
                    exact assump_497
                  let assump_514 := assump_512 assump_603
                  apply False.elim assump_514
    case inr assump_460 =>
      cases assump_2
      case intro assump_520 assump_521 =>
        cases assump_520
        case inl assump_522 =>
          cases assump_522
          case intro assump_524 assump_525 =>
            cases assump_521
            case intro assump_530 assump_531 =>
              cases assump_530
              case intro assump_532 assump_533 =>
                cases assump_1
                case intro assump_540 assump_541 =>
                  apply Or.inr
                  exact assump_524
        case inr assump_523 =>
          cases assump_523
          case intro assump_546 assump_547 =>
            cases assump_521
            case intro assump_552 assump_553 =>
              cases assump_552
              case intro assump_554 assump_555 =>
                cases assump_1
                case intro assump_562 assump_563 =>
                  have assump_604 : ((False ∨ p3) ∨ (p5 → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_555
                  let assump_568 := assump_563 assump_604
                  let assump_569 := And.right assump_568
                  have assump_605 : p1 := by
                    exact assump_554
                  let assump_572 := assump_569 assump_605
                  apply False.elim assump_572


variable (p4 p7 p2 p1 p0 p5 p3 : Prop)
theorem file37_99364 : (((((p3 ∧ p2) → (p2 → p5)) ∧ ((p5 ∨ True) → False)) → False) ∨ ((((p4 → False) → False) → False) ∧ (((p4 ∨ p7) → False) ∧ ((p2 ∧ p0) ∧ (p5 ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (p5 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p5 p6 p3 : Prop)
theorem file37_99803 : (((((p5 ∧ p3) ∨ (True ∧ p6)) → ((True → False) → False)) → False) → False) := by
  intro assump_1
  have assump_37 : (((p5 ∧ p3) ∨ (True ∧ p6)) → ((True → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_38 : True := by
          apply True.intro
        let assump_19 := assump_6 assump_38
        apply False.elim assump_19
    case inr assump_10 =>
      cases assump_10
      case intro assump_23 assump_24 =>
        have assump_39 : True := by
          apply True.intro
        let assump_30 := assump_6 assump_39
        apply False.elim assump_30
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p3 p6 p2 p0 p1 p5 : Prop)
theorem file37_100621 : (((((p3 → True) ∨ (p3 → False)) → False) → (((p3 → False) ∨ (p1 ∨ p1)) → ((p6 → False) ∧ (p0 ∨ p3)))) ∨ ((((p2 ∧ p5) ∧ (p1 → False)) → False) ∨ (((False ∨ p1) ∨ (False ∧ p3)) → ((p6 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    have assump_68 : ((p3 → True) ∨ (p3 → False)) := by
      apply Or.inl
      intro assump_13
      apply True.intro
    let assump_12 := assump_1 assump_68
    apply False.elim assump_12
  case inr assump_7 =>
    cases assump_7
    case inl assump_17 =>
      have assump_69 : ((p3 → True) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_24
        apply True.intro
      let assump_23 := assump_1 assump_69
      apply False.elim assump_23
    case inr assump_18 =>
      have assump_70 : ((p3 → True) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_33
        apply True.intro
      let assump_32 := assump_1 assump_70
      apply False.elim assump_32
  cases assump_2
  case inl assump_37 =>
    have assump_71 : ((p3 → True) ∨ (p3 → False)) := by
      apply Or.inl
      intro assump_44
      apply True.intro
    let assump_43 := assump_1 assump_71
    apply False.elim assump_43
  case inr assump_38 =>
    cases assump_38
    case inl assump_48 =>
      have assump_72 : ((p3 → True) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_55
        apply True.intro
      let assump_54 := assump_1 assump_72
      apply False.elim assump_54
    case inr assump_49 =>
      have assump_73 : ((p3 → True) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_64
        apply True.intro
      let assump_63 := assump_1 assump_73
      apply False.elim assump_63


variable (p2 p4 p3 p5 p1 p6 p7 : Prop)
theorem file37_102442 : (((((p2 ∧ p3) ∨ (p5 → p5)) ∨ ((False → False) → (p5 ∨ p4))) → (((p5 → p1) ∨ (False ∨ p1)) → ((False → False) ∧ (False → False)))) ∨ ((((p1 → False) → (p2 → False)) ∨ ((p5 → False) ∧ (p6 → False))) ∧ (((p2 ∨ p7) ∨ (False ∧ False)) ∧ ((p5 ∧ False) ∧ (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  apply False.elim assump_6


variable (p2 p6 p1 p3 p5 p7 p4 p0 : Prop)
theorem file37_102936 : ((((((p5 → False) ∨ (False ∨ p7)) → False) → (((p1 ∨ False) ∧ (p4 → p3)) ∧ ((p1 ∨ p6) ∧ (p4 → p1)))) ∧ ((((p5 → True) → (p2 ∨ p0)) → ((p2 → False) ∧ (p4 → p7))) ∧ (((p1 ∧ p7) → False) ∧ ((p2 ∧ p6) ∧ (False ∨ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case inl assump_22 =>
              apply False.elim assump_22
            case inr assump_23 =>
              have assump_41 : ((p5 → True) → (p2 ∨ p0)) := by
                intro assump_33
                apply Or.inl
                exact assump_16
              let assump_32 := assump_6 assump_41
              let assump_36 := And.left assump_32
              have assump_42 : p2 := by
                exact assump_16
              let assump_37 := assump_36 assump_42
              apply False.elim assump_37


variable (p6 p7 p0 p5 p2 p1 : Prop)
theorem file37_104104 : ((((((p7 ∨ p1) → (False ∨ False)) → ((p1 ∨ p6) ∧ (False → p7))) → (((p0 ∧ p6) ∧ (False ∧ p5)) → ((p1 → False) ∨ (p2 → p6)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p7 ∨ p1) → (False ∨ False)) → ((p1 ∨ p6) ∧ (False → p7))) → (((p0 ∧ p6) ∧ (False ∧ p5)) → ((p1 → False) ∨ (p2 → p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p6 p3 p5 p7 p1 p0 p4 : Prop)
theorem file37_104804 : ((((((p6 → True) ∨ (p6 → True)) ∨ ((p4 ∧ p5) → (p7 → p3))) ∧ (((p2 ∧ False) → (p5 → p2)) ∧ ((p3 → p7) ∧ (False ∧ p4)))) ∧ ((((p4 ∧ p0) → (p2 → False)) → ((p1 → p6) → (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_12 assump_13 =>
            cases assump_13
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
        case inr assump_9 =>
          cases assump_5
          case intro assump_26 assump_27 =>
            cases assump_27
            case intro assump_30 assump_31 =>
              cases assump_31
              case intro assump_34 assump_35 =>
                apply False.elim assump_34
      case inr assump_7 =>
        cases assump_5
        case intro assump_40 assump_41 =>
          cases assump_41
          case intro assump_44 assump_45 =>
            cases assump_45
            case intro assump_48 assump_49 =>
              apply False.elim assump_48


variable (p5 p1 p2 p4 p6 : Prop)
theorem file37_106124 : (((((False → p1) ∨ (p1 → p6)) ∧ ((p5 ∧ p4) ∨ (False → False))) → False) → ((((p1 → p5) → (p1 → False)) → ((p2 ∧ False) ∨ (p4 → p1))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_17 : (((False → p1) ∨ (p1 → p6)) ∧ ((p5 ∧ p4) ∨ (False → False))) := by
    apply And.intro
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
    apply Or.inr
    intro assump_11
    apply False.elim assump_11
  let assump_7 := assump_1 assump_17
  apply False.elim assump_7


variable (p1 p0 p5 p3 p7 : Prop)
theorem file37_106669 : (((((p1 → False) ∨ (p5 ∨ p3)) → ((False ∨ p0) ∨ (True → False))) ∧ (((p0 ∨ p3) → (p7 ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p0 ∨ p3) → (p7 ∨ True)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inr
        apply True.intro
      case inr assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p7 p5 p3 p6 p4 : Prop)
theorem file37_107225 : (((((p7 → p3) → (p3 → False)) → False) ∧ (((p4 ∧ p5) ∨ (p3 ∧ p3)) ∧ ((p3 → False) ∧ (p6 ∧ p6)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_11
          case intro assump_20 assump_21 =>
            cases assump_21
            case intro assump_24 assump_25 =>
              have assump_75 : ((p7 → p3) → (p3 → False)) := by
                intro assump_36
                intro assump_37
                have assump_76 : p3 := by
                  exact assump_37
                let assump_46 := assump_20 assump_76
                apply False.elim assump_46
              let assump_35 := assump_6 assump_75
              apply False.elim assump_35
      case inr assump_13 =>
        cases assump_13
        case intro assump_53 assump_54 =>
          cases assump_11
          case intro assump_59 assump_60 =>
            cases assump_60
            case intro assump_63 assump_64 =>
              have assump_77 : p3 := by
                exact assump_54
              let assump_71 := assump_59 assump_77
              apply False.elim assump_71


variable (p3 p5 p1 p4 p7 p6 : Prop)
theorem file37_108575 : (((((p5 ∨ True) ∨ (p5 → False)) → False) → (((p1 → p4) → False) ∧ ((False → p6) → False))) ∨ ((((p6 → False) ∧ (p1 → False)) ∧ ((p6 ∨ p3) → False)) ∧ (((p7 ∧ p6) → False) ∧ ((p6 ∧ False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_20 : ((p5 ∨ True) ∨ (p5 → False)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_20
  apply False.elim assump_7
  intro assump_11
  have assump_21 : ((p5 ∨ True) ∨ (p5 → False)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_16 := assump_1 assump_21
  apply False.elim assump_16


variable (p1 p3 p4 : Prop)
theorem file37_109266 : ((((((p3 → False) → False) → False) → (((p1 ∧ True) ∨ (p1 ∧ p4)) ∨ ((p3 → True) ∨ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p3 → False) → False) → False) → (((p1 ∧ True) ∨ (p1 ∧ p4)) ∨ ((p3 → True) ∨ (p3 → False)))) := by
    intro assump_5
    apply Or.inr
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p7 p3 p2 p5 p0 p6 : Prop)
theorem file37_109747 : (((((p0 → True) ∨ (p3 ∨ p5)) ∨ ((True → p6) ∧ (p7 ∧ p6))) ∧ (((p0 → p5) → False) ∧ ((p2 → p4) ∧ (p4 ∧ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              have assump_122 : (p0 → p5) := by
                intro assump_28
                exact assump_19
              let assump_27 := assump_10 assump_122
              apply False.elim assump_27
      case inr assump_7 =>
        cases assump_7
        case inl assump_34 =>
          cases assump_3
          case intro assump_38 assump_39 =>
            cases assump_39
            case intro assump_42 assump_43 =>
              cases assump_43
              case intro assump_46 assump_47 =>
                have assump_123 : (p0 → p5) := by
                  intro assump_56
                  exact assump_47
                let assump_55 := assump_38 assump_123
                apply False.elim assump_55
        case inr assump_35 =>
          cases assump_3
          case intro assump_64 assump_65 =>
            cases assump_65
            case intro assump_68 assump_69 =>
              cases assump_69
              case intro assump_72 assump_73 =>
                have assump_124 : (p0 → p5) := by
                  intro assump_82
                  exact assump_73
                let assump_81 := assump_64 assump_124
                apply False.elim assump_81
    case inr assump_5 =>
      cases assump_5
      case intro assump_88 assump_89 =>
        cases assump_89
        case intro assump_92 assump_93 =>
          cases assump_3
          case intro assump_98 assump_99 =>
            cases assump_99
            case intro assump_102 assump_103 =>
              cases assump_103
              case intro assump_106 assump_107 =>
                have assump_125 : (p0 → p5) := by
                  intro assump_116
                  exact assump_107
                let assump_115 := assump_98 assump_125
                apply False.elim assump_115


variable (p5 p7 p4 p0 p6 p2 p1 : Prop)
theorem file37_112087 : (((((p7 ∨ False) ∨ (p2 ∨ True)) → False) → (((p1 → p2) ∨ (p0 ∨ p4)) ∧ ((p1 ∧ False) ∨ (p5 → p7)))) ∨ ((((p6 → False) ∧ (p2 → p1)) ∧ ((p6 ∧ p1) ∧ (p1 ∧ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_22 : ((p7 ∨ False) ∨ (p2 ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_8 := assump_1 assump_22
  apply False.elim assump_8
  apply Or.inr
  intro assump_14
  have assump_23 : ((p7 ∨ False) ∨ (p2 ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_18 := assump_1 assump_23
  apply False.elim assump_18


variable (p2 p0 p3 p7 p6 p5 p4 p1 : Prop)
theorem file37_112791 : (((((p1 ∨ p4) → False) → False) ∨ (((p2 → p1) → (True ∧ p3)) ∧ ((p1 ∧ p1) ∧ (True → False)))) → ((((p2 ∧ p5) ∧ (False → False)) → ((p6 ∨ p1) ∨ (True → False))) → (((False → p2) → (p7 → p0)) → ((False ∧ p4) → (p3 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p0 p5 p3 p4 p1 : Prop)
theorem file37_113245 : (((((p0 → True) → False) ∨ ((p1 → p5) ∧ (p3 ∧ p4))) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_46
  cases assump_46
  case intro assump_47 assump_48 =>
    cases assump_47
    case inl assump_49 =>
      have assump_89 : ((True → False) → False) := by
        intro assump_56
        have assump_90 : True := by
          apply True.intro
        let assump_59 := assump_56 assump_90
        apply False.elim assump_59
      let assump_55 := assump_48 assump_89
      apply False.elim assump_55
    case inr assump_50 =>
      cases assump_50
      case intro assump_66 assump_67 =>
        cases assump_67
        case intro assump_70 assump_71 =>
          have assump_91 : ((True → False) → False) := by
            intro assump_79
            have assump_92 : True := by
              apply True.intro
            let assump_82 := assump_79 assump_92
            apply False.elim assump_82
          let assump_78 := assump_48 assump_91
          apply False.elim assump_78


variable (p0 p5 p2 p1 : Prop)
theorem file37_114302 : (((((p2 ∧ p0) ∨ (False ∧ p1)) ∨ ((False ∧ p5) → False)) → False) → False) := by
  intro assump_1
  have assump_13 : (((p2 ∧ p0) ∨ (False ∧ p1)) ∨ ((False ∧ p5) → False)) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p2 p4 p6 p5 p0 p1 p3 : Prop)
theorem file37_114732 : ((((((p1 ∧ True) → (True ∧ p0)) ∧ ((p7 → p1) → (p7 → p1))) ∧ (((p6 → p3) ∧ (p3 → p0)) ∧ ((p6 ∨ p4) ∧ (False ∧ p2)))) ∨ ((((True ∨ p5) ∨ (p5 → p6)) → False) ∧ (((False ∧ p6) → False) → ((p1 → p1) ∧ (p5 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_21
                case intro assump_26 assump_27 =>
                  apply False.elim assump_26
              case inr assump_23 =>
                cases assump_21
                case intro assump_32 assump_33 =>
                  apply False.elim assump_32
  case inr assump_3 =>
    cases assump_3
    case intro assump_36 assump_37 =>
      have assump_57 : ((True ∨ p5) ∨ (p5 → p6)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_53 := assump_36 assump_57
      apply False.elim assump_53


variable (p6 p0 p7 p1 p5 : Prop)
theorem file37_116029 : ((((((False ∧ p6) ∧ (p5 → False)) → False) ∨ (((p1 ∨ p0) → False) → ((p5 ∧ p5) ∧ (p5 ∨ p1)))) → ((((False ∨ True) → False) ∧ ((p0 → p1) ∨ (True ∧ p6))) ∧ (((p0 → False) → (p7 → False)) → False))) → False) := by
  intro assump_1
  have assump_18 : ((((False ∧ p6) ∧ (p5 → False)) → False) ∨ (((p1 ∨ p0) → False) → ((p5 ∧ p5) ∧ (p5 ∨ p1)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  let assump_12 := And.left assump_4
  let assump_13 := And.left assump_12
  have assump_19 : (False ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_14 := assump_13 assump_19
  apply False.elim assump_14


variable (p0 p1 p2 p3 p4 p6 : Prop)
theorem file37_116876 : ((((((p0 → False) → (p3 → False)) → ((False ∨ True) ∧ (p2 ∨ True))) → False) ∧ ((((p3 → False) ∨ (p6 ∨ p0)) → ((p0 → p0) ∨ (p4 → p6))) ∧ (((False ∧ p1) → (False ∧ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_25 : ((False ∧ p1) → (False ∧ p0)) := by
        intro assump_13
        apply And.intro
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
        cases assump_13
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
      let assump_12 := assump_7 assump_25
      apply False.elim assump_12


variable (p7 p0 p3 p1 p5 p6 : Prop)
theorem file37_117641 : (((((False → p3) ∨ (p7 ∨ p0)) → ((p5 ∧ p6) ∧ (p7 → p1))) ∧ (((p6 ∨ p0) → (False → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : ((p6 ∨ p0) → (False → False)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p6 p3 p5 p4 p0 p2 p7 p1 : Prop)
theorem file37_118092 : (((((p1 → False) ∧ (False ∧ p5)) ∧ ((p3 → p0) → False)) ∧ (((False ∧ False) → False) → ((p4 ∧ p2) ∨ (True ∨ p1)))) → ((((p0 → False) ∨ (p4 ∧ p1)) ∧ ((False → p7) → (p6 → p7))) ∧ (((p2 → False) ∨ (p0 → True)) → ((p7 → True) ∨ (False → p1))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
  intro assump_14
  intro assump_15
  cases assump_1
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          apply False.elim assump_28
  intro assump_32
  cases assump_32
  case inl assump_33 =>
    cases assump_1
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        cases assump_39
        case intro assump_41 assump_42 =>
          cases assump_42
          case intro assump_45 assump_46 =>
            apply False.elim assump_45
  case inr assump_34 =>
    cases assump_1
    case intro assump_51 assump_52 =>
      cases assump_51
      case intro assump_53 assump_54 =>
        cases assump_53
        case intro assump_55 assump_56 =>
          cases assump_56
          case intro assump_59 assump_60 =>
            apply False.elim assump_59


variable (p3 p6 p2 p7 p0 p5 p1 p4 : Prop)
theorem file37_119710 : (((((p0 ∨ p7) ∨ (True → p6)) ∧ ((False ∧ p3) ∧ (p4 ∨ p1))) ∧ (((p4 → p0) → (p4 ∨ p3)) ∧ ((False ∨ p4) → (p7 ∨ p7)))) → ((((False → p4) ∨ (p6 → p7)) ∨ ((p2 → p3) → (p1 ∧ p6))) → (((False → False) → (p5 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_1
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_15
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  apply False.elim assump_24
            case inr assump_19 =>
              cases assump_15
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  apply False.elim assump_32
          case inr assump_17 =>
            cases assump_15
            case intro assump_38 assump_39 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                apply False.elim assump_40
    case inr assump_9 =>
      cases assump_1
      case intro assump_46 assump_47 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          cases assump_48
          case inl assump_50 =>
            cases assump_50
            case inl assump_52 =>
              cases assump_49
              case intro assump_56 assump_57 =>
                cases assump_56
                case intro assump_58 assump_59 =>
                  apply False.elim assump_58
            case inr assump_53 =>
              cases assump_49
              case intro assump_64 assump_65 =>
                cases assump_64
                case intro assump_66 assump_67 =>
                  apply False.elim assump_66
          case inr assump_51 =>
            cases assump_49
            case intro assump_72 assump_73 =>
              cases assump_72
              case intro assump_74 assump_75 =>
                apply False.elim assump_74
  case inr assump_7 =>
    cases assump_1
    case intro assump_80 assump_81 =>
      cases assump_80
      case intro assump_82 assump_83 =>
        cases assump_82
        case inl assump_84 =>
          cases assump_84
          case inl assump_86 =>
            cases assump_83
            case intro assump_90 assump_91 =>
              cases assump_90
              case intro assump_92 assump_93 =>
                apply False.elim assump_92
          case inr assump_87 =>
            cases assump_83
            case intro assump_98 assump_99 =>
              cases assump_98
              case intro assump_100 assump_101 =>
                apply False.elim assump_100
        case inr assump_85 =>
          cases assump_83
          case intro assump_106 assump_107 =>
            cases assump_106
            case intro assump_108 assump_109 =>
              apply False.elim assump_108


variable (p1 p7 p5 p6 p0 p2 p3 : Prop)
theorem file37_122897 : (((((True ∨ p3) → False) → False) ∨ (((p3 ∧ p0) → (p7 ∧ p0)) → ((p5 → False) ∨ (p1 → False)))) ∨ ((((p1 ∨ p6) ∨ (p3 → p1)) ∧ ((p2 → False) ∨ (False → p2))) ∨ (((True → False) → (p2 → p2)) ∨ ((p7 → p7) → (p5 → p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (True ∨ p3) := by
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p7 p6 p5 p0 p3 : Prop)
theorem file37_123365 : (((((True ∨ p5) → False) ∧ ((p3 ∨ p0) → False)) ∧ (((p4 → False) ∨ (p7 ∧ p0)) ∧ ((p4 ∧ p6) → (p3 ∧ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_40 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_21 := assump_4 assump_40
          apply False.elim assump_21
        case inr assump_13 =>
          cases assump_13
          case intro assump_25 assump_26 =>
            have assump_41 : (p3 ∨ p0) := by
              apply Or.inr
              exact assump_26
            let assump_36 := assump_5 assump_41
            apply False.elim assump_36


