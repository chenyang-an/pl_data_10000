variable (p3 p2 p7 p1 p0 : Prop)
theorem file49_41 : (((((False ∧ p0) ∨ (False ∧ False)) → False) → False) → ((((p1 ∧ p3) ∨ (p7 → p3)) ∧ ((p0 ∨ p0) → (p3 ∧ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        have assump_53 : (((False ∧ p0) ∨ (False ∧ False)) → False) := by
          intro assump_18
          cases assump_18
          case inl assump_19 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              apply False.elim assump_21
          case inr assump_20 =>
            cases assump_20
            case intro assump_25 assump_26 =>
              apply False.elim assump_25
        let assump_17 := assump_1 assump_53
        apply False.elim assump_17
    case inr assump_6 =>
      have assump_54 : (((False ∧ p0) ∨ (False ∧ False)) → False) := by
        intro assump_39
        cases assump_39
        case inl assump_40 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            apply False.elim assump_42
        case inr assump_41 =>
          cases assump_41
          case intro assump_46 assump_47 =>
            apply False.elim assump_46
      let assump_38 := assump_1 assump_54
      apply False.elim assump_38


variable (p4 p0 p5 p1 : Prop)
theorem file49_1405 : ((((((True ∧ p1) ∨ (False ∨ p5)) → ((p4 ∧ p0) → False)) → False) ∧ ((((False → False) ∧ (False ∧ p4)) → ((p5 ∨ p0) → (False ∧ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_58 : (((False → False) ∧ (False ∧ p4)) → ((p5 ∨ p0) → (False ∧ p4))) := by
      intro assump_9
      intro assump_10
      apply And.intro
      cases assump_10
      case inl assump_11 =>
        cases assump_9
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
      case inr assump_12 =>
        cases assump_9
        case intro assump_25 assump_26 =>
          cases assump_26
          case intro assump_29 assump_30 =>
            apply False.elim assump_29
      cases assump_10
      case inl assump_33 =>
        cases assump_9
        case intro assump_37 assump_38 =>
          cases assump_38
          case intro assump_41 assump_42 =>
            apply False.elim assump_41
      case inr assump_34 =>
        cases assump_9
        case intro assump_47 assump_48 =>
          cases assump_48
          case intro assump_51 assump_52 =>
            apply False.elim assump_51
    let assump_8 := assump_3 assump_58
    apply False.elim assump_8


variable (p6 p1 p2 : Prop)
theorem file49_2758 : ((((((p6 → False) → False) → ((True → False) ∧ (p2 → False))) → (((p6 → False) ∨ (p6 ∧ True)) → ((False → True) ∨ (True ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p6 → False) → False) → ((True → False) ∧ (p2 → False))) → (((p6 → False) ∨ (p6 ∧ True)) → ((False → True) ∨ (True ∧ p1)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      intro assump_13
      apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_14 assump_15 =>
        apply Or.inl
        intro assump_22
        apply True.intro
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p5 p3 p6 p1 p4 p0 : Prop)
theorem file49_3507 : ((((((p4 → False) ∧ (False ∧ p5)) → ((False → False) → (p5 → p5))) → (((p4 ∨ p6) ∨ (False → False)) → False)) ∧ ((((True → False) ∨ (p6 ∧ p3)) ∧ ((p5 → p1) ∨ (p6 → False))) ∧ (((p6 → False) ∨ (p1 → False)) ∧ ((p4 ∧ p0) → (p6 ∨ p6))))) → False) := by
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
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                have assump_149 : True := by
                  apply True.intro
                let assump_29 := assump_10 assump_149
                apply False.elim assump_29
              case inr assump_21 =>
                have assump_150 : True := by
                  apply True.intro
                let assump_40 := assump_10 assump_150
                apply False.elim assump_40
          case inr assump_15 =>
            cases assump_7
            case intro assump_46 assump_47 =>
              cases assump_46
              case inl assump_48 =>
                have assump_151 : True := by
                  apply True.intro
                let assump_57 := assump_10 assump_151
                apply False.elim assump_57
              case inr assump_49 =>
                have assump_152 : True := by
                  apply True.intro
                let assump_68 := assump_10 assump_152
                apply False.elim assump_68
        case inr assump_11 =>
          cases assump_11
          case intro assump_72 assump_73 =>
            cases assump_9
            case inl assump_78 =>
              cases assump_7
              case intro assump_82 assump_83 =>
                cases assump_82
                case inl assump_84 =>
                  have assump_153 : p6 := by
                    exact assump_72
                  let assump_91 := assump_84 assump_153
                  apply False.elim assump_91
                case inr assump_85 =>
                  have assump_154 : (((p4 → False) ∧ (False ∧ p5)) → ((False → False) → (p5 → p5))) := by
                    intro assump_105
                    intro assump_106
                    intro assump_107
                    cases assump_105
                    case intro assump_112 assump_113 =>
                      cases assump_113
                      case intro assump_116 assump_117 =>
                        apply False.elim assump_116
                  let assump_104 := assump_2 assump_154
                  have assump_155 : ((p4 ∨ p6) ∨ (False → False)) := by
                    apply Or.inl
                    apply Or.inr
                    exact assump_72
                  let assump_120 := assump_104 assump_155
                  apply False.elim assump_120
            case inr assump_79 =>
              cases assump_7
              case intro assump_126 assump_127 =>
                cases assump_126
                case inl assump_128 =>
                  have assump_156 : p6 := by
                    exact assump_72
                  let assump_135 := assump_128 assump_156
                  apply False.elim assump_135
                case inr assump_129 =>
                  have assump_157 : p6 := by
                    exact assump_72
                  let assump_145 := assump_79 assump_157
                  apply False.elim assump_145


variable (p5 p1 p3 p2 : Prop)
theorem file49_7107 : ((((((False → False) → False) ∧ ((p5 ∨ p3) ∧ (p1 ∨ p2))) → False) → False) → False) := by
  intro assump_1
  have assump_69 : ((((False → False) → False) ∧ ((p5 ∨ p3) ∧ (p1 ∨ p2))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case inl assump_16 =>
            have assump_70 : (False → False) := by
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_6 assump_70
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_71 : (False → False) := by
              intro assump_34
              apply False.elim assump_34
            let assump_33 := assump_6 assump_71
            apply False.elim assump_33
        case inr assump_13 =>
          cases assump_11
          case inl assump_42 =>
            have assump_72 : (False → False) := by
              intro assump_49
              apply False.elim assump_49
            let assump_48 := assump_6 assump_72
            apply False.elim assump_48
          case inr assump_43 =>
            have assump_73 : (False → False) := by
              intro assump_60
              apply False.elim assump_60
            let assump_59 := assump_6 assump_73
            apply False.elim assump_59
  let assump_4 := assump_1 assump_69
  apply False.elim assump_4


variable (p2 p5 p4 p1 p0 p6 : Prop)
theorem file49_8663 : (((((True ∧ False) ∧ (p6 ∧ False)) ∨ ((False → p2) → False)) → (((p4 ∨ p5) → False) ∧ ((p0 → False) → False))) ∨ ((((p2 ∧ True) → False) ∧ ((True → p6) ∨ (p1 ∧ p1))) → (((p5 → True) ∨ (p6 → False)) ∨ ((p6 → False) ∨ (False ∧ p2))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          apply False.elim assump_12
    case inr assump_8 =>
      have assump_69 : (False → p2) := by
        intro assump_20
        apply False.elim assump_20
      let assump_19 := assump_8 assump_69
      apply False.elim assump_19
  case inr assump_4 =>
    cases assump_1
    case inl assump_28 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          apply False.elim assump_33
    case inr assump_29 =>
      have assump_70 : (False → p2) := by
        intro assump_41
        apply False.elim assump_41
      let assump_40 := assump_29 assump_70
      apply False.elim assump_40
  intro assump_47
  cases assump_1
  case inl assump_50 =>
    cases assump_50
    case intro assump_52 assump_53 =>
      cases assump_52
      case intro assump_54 assump_55 =>
        apply False.elim assump_55
  case inr assump_51 =>
    have assump_71 : (False → p2) := by
      intro assump_63
      apply False.elim assump_63
    let assump_62 := assump_51 assump_71
    apply False.elim assump_62


variable (p3 p7 p1 p2 p6 p0 p5 : Prop)
theorem file49_10320 : (((((False ∧ p2) ∧ (p5 → p0)) ∧ ((p3 ∨ False) → (p1 ∨ True))) → False) ∨ ((((p5 ∨ p7) → False) ∨ ((p7 → p6) → False)) ∨ (((p2 → p7) → (p2 ∧ False)) → ((True → False) ∨ (p5 ∨ p6))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6


variable (p2 p4 p0 p3 p5 p1 p6 p7 : Prop)
theorem file49_10805 : ((((((p0 → False) → (p4 ∨ p7)) ∧ ((p0 → False) → False)) ∧ (((p6 ∨ p5) → False) ∨ ((p3 ∧ p7) → (p4 ∧ p2)))) ∧ ((((p6 → False) ∧ (False ∧ p1)) ∧ ((p4 ∨ p1) → False)) ∧ (((p4 ∨ p4) ∧ (p0 ∧ p2)) → ((p7 ∨ p6) ∧ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case inl assump_12 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  apply False.elim assump_24
        case inr assump_13 =>
          cases assump_3
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                cases assump_35
                case intro assump_38 assump_39 =>
                  apply False.elim assump_38


variable (p4 p1 p0 p7 p3 : Prop)
theorem file49_12062 : (((((p3 ∨ p1) → False) → ((p7 ∧ p0) → False)) → False) → ((((p3 → True) ∧ (False ∧ p7)) → ((True ∨ p1) → (p7 ∧ p0))) ∨ (((p4 → False) ∧ (True ∧ p3)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply And.intro
  cases assump_5
  case inl assump_6 =>
    cases assump_4
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
  case inr assump_7 =>
    cases assump_4
    case intro assump_20 assump_21 =>
      cases assump_21
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
  cases assump_5
  case inl assump_28 =>
    cases assump_4
    case intro assump_32 assump_33 =>
      cases assump_33
      case intro assump_36 assump_37 =>
        apply False.elim assump_36
  case inr assump_29 =>
    cases assump_4
    case intro assump_42 assump_43 =>
      cases assump_43
      case intro assump_46 assump_47 =>
        apply False.elim assump_46


variable (p1 p5 p6 p2 p0 p3 : Prop)
theorem file49_13116 : (((((p0 ∧ p5) ∧ (p2 → False)) → ((p2 ∨ p0) → False)) ∧ (((False → False) → False) ∧ ((False → p6) → (p1 ∧ p5)))) → ((((False ∧ p6) → (p2 ∨ p3)) → False) ∨ (((False → p3) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      have assump_30 : (False → False) := by
        intro assump_24
        apply False.elim assump_24
      let assump_23 := assump_6 assump_30
      apply False.elim assump_23


variable (p6 p7 p4 p2 p0 p5 : Prop)
theorem file49_13715 : (((((False → False) → (p0 ∨ True)) → ((p6 → False) ∧ (p7 → False))) ∧ (((p5 → False) → False) → False)) → ((((p0 ∨ p2) → False) → False) → (((p5 ∧ p4) ∨ (False ∧ p6)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        have assump_35 : ((p5 → False) → False) := by
          intro assump_21
          have assump_36 : p5 := by
            exact assump_6
          let assump_24 := assump_21 assump_36
          apply False.elim assump_24
        let assump_20 := assump_15 assump_35
        apply False.elim assump_20
  case inr assump_5 =>
    cases assump_5
    case intro assump_31 assump_32 =>
      apply False.elim assump_31


variable (p0 p5 p6 p4 p1 p7 p2 p3 : Prop)
theorem file49_14592 : (((((p1 → False) ∨ (p4 → False)) → ((p0 ∨ p5) ∨ (False → p7))) ∨ (((False → p0) → False) ∧ ((False → False) ∧ (p4 → False)))) ∨ ((((p2 ∨ p3) ∧ (p5 → p1)) ∧ ((p6 ∧ p0) ∧ (p1 → p7))) ∨ (((p7 → False) → (p4 → p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_30
  cases assump_30
  case inl assump_31 =>
    apply Or.inr
    intro assump_35
    apply False.elim assump_35
  case inr assump_32 =>
    apply Or.inr
    intro assump_40
    apply False.elim assump_40


variable (p6 p2 p5 p0 p3 p7 p4 : Prop)
theorem file49_15133 : (((((p0 ∧ True) → (p3 → p3)) ∨ ((p4 ∨ p7) → False)) → False) → ((((p3 ∧ p4) → (p3 → False)) ∨ ((p5 ∨ p5) → (False → False))) ∧ (((p0 ∨ p4) ∨ (p0 ∧ p2)) ∧ ((False ∧ p6) → (p6 → False))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    have assump_55 : (((p0 ∧ True) → (p3 → p3)) ∨ ((p4 ∨ p7) → False)) := by
      apply Or.inl
      intro assump_18
      intro assump_19
      cases assump_18
      case intro assump_22 assump_23 =>
        exact assump_19
    let assump_17 := assump_1 assump_55
    apply False.elim assump_17
  apply And.intro
  have assump_56 : (((p0 ∧ True) → (p3 → p3)) ∨ ((p4 ∨ p7) → False)) := by
    apply Or.inl
    intro assump_34
    intro assump_35
    cases assump_34
    case intro assump_38 assump_39 =>
      exact assump_35
  let assump_33 := assump_1 assump_56
  apply False.elim assump_33
  intro assump_47
  intro assump_48
  cases assump_47
  case intro assump_51 assump_52 =>
    apply False.elim assump_51


variable (p1 p0 p6 p2 p3 p4 p5 : Prop)
theorem file49_16239 : ((((((False → False) → False) ∧ ((p5 ∧ p0) ∧ (p3 → False))) → (((p1 → False) ∨ (p2 ∧ p5)) → ((p6 → p4) ∨ (p6 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_76 : ((((False → False) → False) ∧ ((p5 ∧ p0) ∧ (p3 → False))) → (((p1 → False) ∨ (p2 ∧ p5)) → ((p6 → p4) ∨ (p6 ∨ False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply Or.inl
            intro assump_25
            have assump_77 : (False → False) := by
              intro assump_33
              apply False.elim assump_33
            let assump_32 := assump_11 assump_77
            apply False.elim assump_32
    case inr assump_8 =>
      cases assump_8
      case intro assump_39 assump_40 =>
        cases assump_5
        case intro assump_45 assump_46 =>
          cases assump_46
          case intro assump_49 assump_50 =>
            cases assump_49
            case intro assump_51 assump_52 =>
              apply Or.inl
              intro assump_59
              have assump_78 : (False → False) := by
                intro assump_67
                apply False.elim assump_67
              let assump_66 := assump_45 assump_78
              apply False.elim assump_66
  let assump_4 := assump_1 assump_76
  apply False.elim assump_4


variable (p6 p5 p1 p0 p4 p3 p7 p2 : Prop)
theorem file49_17790 : (((((False ∨ p4) → (p3 → p7)) → False) → (((p1 ∨ p7) → False) → ((p4 ∨ False) ∨ (True ∨ p6)))) ∨ ((((p7 ∨ True) ∧ (p3 → False)) ∧ ((p5 → p0) ∧ (p7 ∨ p3))) ∧ (((p4 → False) ∧ (True ∨ p5)) ∨ ((p3 ∧ p2) ∨ (p3 ∧ p2))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p5 p7 p1 p0 p4 : Prop)
theorem file49_18167 : ((((((p7 ∧ False) ∧ (True ∧ p5)) ∨ ((True → False) → False)) ∨ (((p0 → p5) → (p4 → False)) → ((p1 → False) ∨ (p0 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p7 ∧ False) ∧ (True ∧ p5)) ∨ ((True → False) → False)) ∨ (((p0 → p5) → (p4 → False)) → ((p1 → False) ∨ (p0 ∧ False)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p3 p6 p7 p0 p1 p2 p4 : Prop)
theorem file49_18789 : (((((False ∧ p6) → (p7 ∧ p7)) ∧ ((p4 ∧ p2) ∧ (p0 ∧ p6))) → (((p5 → False) → False) → ((p2 → False) ∧ (p2 → False)))) → ((((False → p3) → (p1 → False)) → ((True ∨ p4) ∧ (False ∨ True))) ∨ (((p3 ∧ p1) → (p3 ∨ False)) → ((True → False) → (True ∧ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  apply Or.inl
  apply True.intro
  apply Or.inr
  apply True.intro


variable (p3 p2 p0 p4 p6 p7 p5 : Prop)
theorem file49_19247 : (((((False ∨ True) → False) ∧ ((p3 ∨ p6) ∨ (p2 → p0))) → False) ∨ ((((p7 ∨ p2) → False) → False) ∧ (((p4 ∧ p0) → (True ∨ p5)) ∧ ((True ∨ p6) → (p5 → p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_31 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_13 := assump_2 assump_31
        apply False.elim assump_13
      case inr assump_9 =>
        have assump_32 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_20 := assump_2 assump_32
        apply False.elim assump_20
    case inr assump_7 =>
      have assump_33 : (False ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_27 := assump_2 assump_33
      apply False.elim assump_27


variable (p7 p4 p6 p3 p5 : Prop)
theorem file49_20209 : ((((((p7 → p3) → False) ∧ ((p4 ∨ p5) → False)) → (((p6 ∧ p7) ∨ (p4 → True)) → ((p3 ∨ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_85 : ((((p7 → p3) → False) ∧ ((p4 ∨ p5) → False)) → (((p6 ∧ p7) ∨ (p4 → True)) → ((p3 ∨ p5) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_6
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_5
          case intro assump_20 assump_21 =>
            have assump_86 : (p7 → p3) := by
              intro assump_28
              exact assump_8
            let assump_27 := assump_20 assump_86
            apply False.elim assump_27
      case inr assump_13 =>
        cases assump_5
        case intro assump_36 assump_37 =>
          have assump_87 : (p7 → p3) := by
            intro assump_44
            exact assump_8
          let assump_43 := assump_36 assump_87
          apply False.elim assump_43
    case inr assump_9 =>
      cases assump_6
      case inl assump_52 =>
        cases assump_52
        case intro assump_54 assump_55 =>
          cases assump_5
          case intro assump_60 assump_61 =>
            have assump_88 : (p4 ∨ p5) := by
              apply Or.inr
              exact assump_9
            let assump_66 := assump_61 assump_88
            apply False.elim assump_66
      case inr assump_53 =>
        cases assump_5
        case intro assump_72 assump_73 =>
          have assump_89 : (p4 ∨ p5) := by
            apply Or.inr
            exact assump_9
          let assump_78 := assump_73 assump_89
          apply False.elim assump_78
  let assump_4 := assump_1 assump_85
  apply False.elim assump_4


variable (p2 : Prop)
theorem file49_22005 : (((((False ∧ p2) ∧ (p2 ∨ p2)) → False) → False) → False) := by
  intro assump_36
  have assump_50 : (((False ∧ p2) ∧ (p2 ∨ p2)) → False) := by
    intro assump_40
    cases assump_40
    case intro assump_41 assump_42 =>
      cases assump_41
      case intro assump_43 assump_44 =>
        apply False.elim assump_43
  let assump_39 := assump_36 assump_50
  apply False.elim assump_39


variable (p5 p2 p6 p7 p1 p4 p3 : Prop)
theorem file49_22454 : ((((((p4 → False) ∧ (p5 → False)) ∨ ((p2 ∧ p6) → (p1 ∧ p1))) → (((p4 → False) → (p4 → False)) → ((p7 → p3) → (p3 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p4 → False) ∧ (p5 → False)) ∨ ((p2 ∧ p6) → (p1 ∧ p1))) → (((p4 → False) → (p4 → False)) → ((p7 → p3) → (p3 ∨ True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply Or.inr
        apply True.intro
    case inr assump_13 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p6 p2 p3 p0 p4 : Prop)
theorem file49_23166 : ((((((p3 → False) ∨ (True → True)) ∧ ((p0 → False) ∧ (p2 ∨ p6))) → False) ∧ ((((p0 ∨ p2) ∧ (p3 ∨ p3)) ∨ ((p4 → False) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p0 ∨ p2) ∧ (p3 ∨ p3)) ∨ ((p4 → False) → (False → False))) := by
      apply Or.inr
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p4 p0 p6 p7 p1 p3 p5 : Prop)
theorem file49_23712 : (((((True ∨ p5) → (p4 ∨ p5)) ∧ ((p6 → True) ∨ (p3 → True))) ∧ (((False ∨ False) ∨ (p0 ∨ p6)) ∨ ((p3 → False) ∧ (p1 ∨ p5)))) → ((((p5 ∧ p3) → (p7 ∨ True)) ∨ ((p4 ∨ True) → (p6 → p5))) ∨ (((p4 → False) ∧ (False → False)) → ((p0 ∨ p6) ∨ (True ∨ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              apply False.elim assump_16
            case inr assump_17 =>
              apply False.elim assump_17
          case inr assump_15 =>
            cases assump_15
            case inl assump_22 =>
              apply Or.inl
              apply Or.inl
              intro assump_26
              cases assump_26
              case intro assump_27 assump_28 =>
                apply Or.inr
                apply True.intro
            case inr assump_23 =>
              apply Or.inl
              apply Or.inl
              intro assump_35
              cases assump_35
              case intro assump_36 assump_37 =>
                apply Or.inr
                apply True.intro
        case inr assump_13 =>
          cases assump_13
          case intro assump_42 assump_43 =>
            cases assump_43
            case inl assump_46 =>
              apply Or.inl
              apply Or.inl
              intro assump_50
              cases assump_50
              case intro assump_51 assump_52 =>
                apply Or.inr
                apply True.intro
            case inr assump_47 =>
              apply Or.inl
              apply Or.inl
              intro assump_59
              cases assump_59
              case intro assump_60 assump_61 =>
                apply Or.inr
                apply True.intro
      case inr assump_9 =>
        cases assump_3
        case inl assump_68 =>
          cases assump_68
          case inl assump_70 =>
            cases assump_70
            case inl assump_72 =>
              apply False.elim assump_72
            case inr assump_73 =>
              apply False.elim assump_73
          case inr assump_71 =>
            cases assump_71
            case inl assump_78 =>
              apply Or.inl
              apply Or.inl
              intro assump_82
              cases assump_82
              case intro assump_83 assump_84 =>
                apply Or.inr
                apply True.intro
            case inr assump_79 =>
              apply Or.inl
              apply Or.inl
              intro assump_91
              cases assump_91
              case intro assump_92 assump_93 =>
                apply Or.inr
                apply True.intro
        case inr assump_69 =>
          cases assump_69
          case intro assump_98 assump_99 =>
            cases assump_99
            case inl assump_102 =>
              apply Or.inl
              apply Or.inl
              intro assump_106
              cases assump_106
              case intro assump_107 assump_108 =>
                apply Or.inr
                apply True.intro
            case inr assump_103 =>
              apply Or.inl
              apply Or.inl
              intro assump_115
              cases assump_115
              case intro assump_116 assump_117 =>
                apply Or.inr
                apply True.intro


variable (p5 p7 p0 p3 : Prop)
theorem file49_27248 : (((((p0 → False) → (False → p7)) ∧ ((True → False) → (p3 ∧ p5))) → False) → False) := by
  intro assump_1
  have assump_25 : (((p0 → False) → (False → p7)) ∧ ((True → False) → (p3 ∧ p5))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    apply And.intro
    have assump_26 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_26
    apply False.elim assump_12
    have assump_27 : True := by
      apply True.intro
    let assump_18 := assump_9 assump_27
    apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p7 p2 p4 p0 p5 p3 : Prop)
theorem file49_27946 : (((((p5 → p0) → False) → False) → False) → ((((p7 ∨ p2) → False) → ((False ∨ p0) → False)) ∨ (((p3 ∧ p5) → (True ∧ p2)) ∧ ((p4 ∧ False) → (p3 ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    apply False.elim assump_6
  case inr assump_7 =>
    have assump_30 : (((p5 → p0) → False) → False) := by
      intro assump_17
      have assump_31 : (p5 → p0) := by
        intro assump_21
        exact assump_7
      let assump_20 := assump_17 assump_31
      apply False.elim assump_20
    let assump_16 := assump_1 assump_30
    apply False.elim assump_16


variable (p7 p1 p0 p5 : Prop)
theorem file49_28629 : ((((((p1 ∨ p5) → False) ∧ ((p7 ∧ p0) ∧ (p0 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p1 ∨ p5) → False) ∧ ((p7 ∧ p0) ∧ (p0 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_28 : p0 := by
            exact assump_13
          let assump_20 := assump_11 assump_28
          apply False.elim assump_20
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p4 p7 p5 p1 p3 p0 p2 p6 : Prop)
theorem file49_29299 : (((((p2 ∨ p4) → (p0 → p5)) → ((p4 → False) ∧ (p1 ∨ p3))) ∧ (((False ∧ p7) → (p5 → p2)) → ((p1 → False) ∧ (False ∧ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : ((False ∧ p7) → (p5 → p2)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    let assump_8 := assump_3 assump_23
    let assump_17 := And.right assump_8
    let assump_19 := And.left assump_17
    apply False.elim assump_19


variable (p6 p4 p5 p2 p1 p3 p7 p0 : Prop)
theorem file49_29912 : ((((((p4 ∧ False) ∧ (p3 → False)) ∧ ((p0 ∧ p7) → (p0 → p6))) → (((p2 ∨ p5) ∧ (False → False)) ∧ ((p5 → False) → (p1 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p4 ∧ False) ∧ (p3 → False)) ∧ ((p0 ∧ p7) → (p0 → p6))) → (((p2 ∨ p5) ∧ (False → False)) ∧ ((p5 → False) → (p1 ∨ False)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
    intro assump_16
    apply False.elim assump_16
    intro assump_19
    cases assump_5
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          apply False.elim assump_27
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p1 p3 p0 p5 p2 p6 : Prop)
theorem file49_30925 : (((((p1 ∨ p1) → False) → ((p1 ∨ False) → (p3 ∨ p0))) ∧ (((p1 ∨ p3) ∧ (p3 → p5)) → ((p2 ∧ p2) → False))) → ((((False ∧ p1) ∧ (p2 ∧ p2)) → ((p3 → p6) ∧ (p0 → False))) ∨ (((p0 ∧ True) → False) → ((p3 ∨ p6) ∨ (p6 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    apply And.intro
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    intro assump_18
    cases assump_8
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        apply False.elim assump_23


variable (p0 p1 p2 p7 p6 p5 : Prop)
theorem file49_31684 : (((((p2 ∨ p7) ∨ (p6 → p1)) ∨ ((p6 → False) → False)) ∨ (((p2 → False) ∨ (p7 ∨ p1)) → ((True → False) ∨ (p5 → p1)))) → ((((p7 → False) → (p1 → False)) ∨ ((p7 → False) ∨ (p1 → False))) → (((True ∧ True) ∧ (p0 ∧ p5)) → ((p7 ∧ False) ∨ (p5 ∧ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_5
      case intro assump_12 assump_13 =>
        cases assump_2
        case inl assump_18 =>
          cases assump_1
          case inl assump_22 =>
            cases assump_22
            case inl assump_24 =>
              cases assump_24
              case inl assump_26 =>
                cases assump_26
                case inl assump_28 =>
                  apply Or.inr
                  apply And.intro
                  exact assump_13
                  apply True.intro
                case inr assump_29 =>
                  apply Or.inr
                  apply And.intro
                  exact assump_13
                  apply True.intro
              case inr assump_27 =>
                apply Or.inr
                apply And.intro
                exact assump_13
                apply True.intro
            case inr assump_25 =>
              apply Or.inr
              apply And.intro
              exact assump_13
              apply True.intro
          case inr assump_23 =>
            apply Or.inr
            apply And.intro
            exact assump_13
            apply True.intro
        case inr assump_19 =>
          cases assump_19
          case inl assump_40 =>
            cases assump_1
            case inl assump_44 =>
              cases assump_44
              case inl assump_46 =>
                cases assump_46
                case inl assump_48 =>
                  cases assump_48
                  case inl assump_50 =>
                    apply Or.inr
                    apply And.intro
                    exact assump_13
                    apply True.intro
                  case inr assump_51 =>
                    apply Or.inr
                    apply And.intro
                    exact assump_13
                    apply True.intro
                case inr assump_49 =>
                  apply Or.inr
                  apply And.intro
                  exact assump_13
                  apply True.intro
              case inr assump_47 =>
                apply Or.inr
                apply And.intro
                exact assump_13
                apply True.intro
            case inr assump_45 =>
              apply Or.inr
              apply And.intro
              exact assump_13
              apply True.intro
          case inr assump_41 =>
            cases assump_1
            case inl assump_64 =>
              cases assump_64
              case inl assump_66 =>
                cases assump_66
                case inl assump_68 =>
                  cases assump_68
                  case inl assump_70 =>
                    apply Or.inr
                    apply And.intro
                    exact assump_13
                    apply True.intro
                  case inr assump_71 =>
                    apply Or.inr
                    apply And.intro
                    exact assump_13
                    apply True.intro
                case inr assump_69 =>
                  apply Or.inr
                  apply And.intro
                  exact assump_13
                  apply True.intro
              case inr assump_67 =>
                apply Or.inr
                apply And.intro
                exact assump_13
                apply True.intro
            case inr assump_65 =>
              apply Or.inr
              apply And.intro
              exact assump_13
              apply True.intro


variable (p7 p2 : Prop)
theorem file49_35556 : ((((((False → False) → False) → False) ∨ (((p7 → False) ∨ (p7 → p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((p7 → False) ∨ (p7 → p2)) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p2 p3 p5 p4 p1 p7 : Prop)
theorem file49_36107 : (((((False ∧ p7) → (p5 ∨ p2)) ∨ ((p6 ∨ False) ∨ (p4 ∨ p2))) → False) → ((((p1 ∨ p1) → False) ∨ ((p6 → p3) ∧ (p3 → False))) → (((p6 → p1) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    have assump_38 : (((False ∧ p7) → (p5 ∨ p2)) ∨ ((p6 ∨ False) ∨ (p4 ∨ p2))) := by
      apply Or.inl
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    let assump_12 := assump_1 assump_38
    apply False.elim assump_12
  case inr assump_7 =>
    cases assump_7
    case intro assump_21 assump_22 =>
      have assump_39 : (((False ∧ p7) → (p5 ∨ p2)) ∨ ((p6 ∨ False) ∨ (p4 ∨ p2))) := by
        apply Or.inl
        intro assump_30
        cases assump_30
        case intro assump_31 assump_32 =>
          apply False.elim assump_31
      let assump_29 := assump_1 assump_39
      apply False.elim assump_29


variable (p5 p0 p4 p6 : Prop)
theorem file49_37099 : ((((((p6 ∨ p0) ∧ (p6 → False)) ∧ ((p6 ∧ p5) → False)) → False) ∧ ((((p4 → False) → (True → False)) → False) ∧ (((p6 → False) ∨ (True ∨ p6)) ∧ ((False → False) ∧ (p4 ∧ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              have assump_105 : ((p4 → False) → (True → False)) := by
                intro assump_31
                intro assump_32
                have assump_106 : p4 := by
                  exact assump_21
                let assump_37 := assump_31 assump_106
                apply False.elim assump_37
              let assump_30 := assump_6 assump_105
              apply False.elim assump_30
        case inr assump_13 =>
          cases assump_13
          case inl assump_44 =>
            cases assump_11
            case intro assump_48 assump_49 =>
              cases assump_49
              case intro assump_52 assump_53 =>
                have assump_107 : ((p4 → False) → (True → False)) := by
                  intro assump_62
                  intro assump_63
                  have assump_108 : p4 := by
                    exact assump_53
                  let assump_68 := assump_62 assump_108
                  apply False.elim assump_68
                let assump_61 := assump_6 assump_107
                apply False.elim assump_61
          case inr assump_45 =>
            cases assump_11
            case intro assump_77 assump_78 =>
              cases assump_78
              case intro assump_81 assump_82 =>
                have assump_109 : ((p4 → False) → (True → False)) := by
                  intro assump_92
                  intro assump_93
                  have assump_110 : p4 := by
                    exact assump_82
                  let assump_98 := assump_92 assump_110
                  apply False.elim assump_98
                let assump_91 := assump_6 assump_109
                apply False.elim assump_91


variable (p7 p0 p4 p2 p3 : Prop)
theorem file49_39388 : ((((((False → False) ∨ (p0 ∧ p7)) → False) → (((p4 ∨ p3) ∧ (p0 → p4)) ∧ ((p2 ∧ p7) → False))) → False) → False) := by
  intro assump_12
  have assump_57 : ((((False → False) ∨ (p0 ∧ p7)) → False) → (((p4 ∨ p3) ∧ (p0 → p4)) ∧ ((p2 ∧ p7) → False))) := by
    intro assump_16
    apply And.intro
    apply And.intro
    have assump_58 : ((False → False) ∨ (p0 ∧ p7)) := by
      apply Or.inl
      intro assump_20
      apply False.elim assump_20
    let assump_19 := assump_16 assump_58
    apply False.elim assump_19
    intro assump_26
    have assump_59 : ((False → False) ∨ (p0 ∧ p7)) := by
      apply Or.inl
      intro assump_32
      apply False.elim assump_32
    let assump_31 := assump_16 assump_59
    apply False.elim assump_31
    intro assump_38
    cases assump_38
    case intro assump_39 assump_40 =>
      have assump_60 : ((False → False) ∨ (p0 ∧ p7)) := by
        apply Or.inl
        intro assump_48
        apply False.elim assump_48
      let assump_47 := assump_16 assump_60
      apply False.elim assump_47
  let assump_15 := assump_12 assump_57
  apply False.elim assump_15


variable (p4 p5 p2 p0 p7 p6 p1 : Prop)
theorem file49_40551 : ((((((False → p6) → False) ∧ ((p0 ∨ p5) → (True ∧ p2))) → (((p1 → p2) ∨ (p7 ∨ True)) ∨ ((p0 ∧ p2) ∧ (p1 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((False → p6) → False) ∧ ((p0 ∨ p5) → (True ∧ p2))) → (((p1 → p2) ∨ (p7 ∨ True)) ∨ ((p0 ∧ p2) ∧ (p1 ∨ p4)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      have assump_28 : (False → p6) := by
        intro assump_18
        apply False.elim assump_18
      let assump_17 := assump_6 assump_28
      apply False.elim assump_17
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p3 p1 p4 p6 : Prop)
theorem file49_41270 : (((((False ∧ p3) ∨ (p1 ∧ False)) ∧ ((p1 → False) ∧ (p6 → p3))) ∧ (((p1 → False) → False) → ((False → p4) ∨ (p3 → False)))) → False) := by
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          apply False.elim assump_24
      case inr assump_23 =>
        cases assump_23
        case intro assump_28 assump_29 =>
          apply False.elim assump_29


variable (p2 p1 p3 p5 p6 p7 p0 p4 : Prop)
theorem file49_41888 : ((((((True → False) ∨ (p0 ∧ False)) ∨ ((p6 ∨ p1) → (True ∧ p5))) → (((p4 → False) ∨ (p6 → False)) → ((p2 → False) ∨ (p5 ∧ p3)))) ∧ ((((p7 ∨ p4) ∨ (p4 → False)) ∨ ((False ∧ p6) ∨ (True → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p7 ∨ p4) ∨ (p4 → False)) ∨ ((False ∧ p6) ∨ (True → False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_9
      have assump_21 : (((p7 ∨ p4) ∨ (p4 → False)) ∨ ((False ∧ p6) ∨ (True → False))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        exact assump_9
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p3 p7 p6 p4 p2 : Prop)
theorem file49_42704 : (((((True → p3) ∧ (False → False)) → ((False → p3) → False)) → (((p4 → p4) → (p7 → False)) → False)) → ((((p3 ∧ p7) ∧ (p7 ∨ p7)) → ((p4 ∨ p4) → False)) → (((False ∧ p6) → False) ∨ ((p2 → p6) ∨ (p2 → p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p5 p0 p6 p2 p4 : Prop)
theorem file49_43121 : (((((True ∧ p4) ∧ (p4 ∨ p5)) ∨ ((p4 → False) ∨ (p5 ∧ p2))) → False) → ((((p6 ∧ p2) → (p4 ∧ p0)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_19 : (((True ∧ p4) ∧ (p4 ∨ p5)) ∨ ((p4 → False) ∨ (p5 ∧ p2))) := by
    apply Or.inr
    apply Or.inl
    intro assump_8
    have assump_20 : (((True ∧ p4) ∧ (p4 ∨ p5)) ∨ ((p4 → False) ∨ (p5 ∧ p2))) := by
      apply Or.inl
      apply And.intro
      apply And.intro
      apply True.intro
      exact assump_8
      apply Or.inl
      exact assump_8
    let assump_12 := assump_1 assump_20
    apply False.elim assump_12
  let assump_7 := assump_1 assump_19
  apply False.elim assump_7


variable (p1 p4 p5 p3 p0 : Prop)
theorem file49_43835 : (((((False ∧ p0) ∧ (p3 → p1)) ∧ ((p5 ∧ p4) ∨ (False ∨ False))) → False) ∧ ((((p4 → p3) → False) → ((p3 ∧ p4) ∨ (p3 → False))) → (((True ∧ False) → False) ∨ ((p3 ∨ p3) → False)))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6
  intro assump_10
  apply Or.inl
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    apply False.elim assump_15


variable (p0 p4 p1 p6 p5 p2 : Prop)
theorem file49_44450 : ((((((True ∨ p1) ∧ (False → False)) ∨ ((p5 ∧ p1) ∧ (p1 → p4))) ∨ (((p5 ∧ p2) → False) → ((p6 → False) → (p0 ∨ p6)))) → False) → False) := by
  intro assump_18
  have assump_28 : ((((True ∨ p1) ∧ (False → False)) ∨ ((p5 ∧ p1) ∧ (p1 → p4))) ∨ (((p5 ∧ p2) → False) → ((p6 → False) → (p0 ∨ p6)))) := by
    apply Or.inl
    apply Or.inl
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_22
    apply False.elim assump_22
  let assump_21 := assump_18 assump_28
  apply False.elim assump_21


variable (p5 p6 p2 p4 p0 : Prop)
theorem file49_45017 : (((((p0 ∨ p5) ∨ (p6 ∨ True)) → False) ∧ (((p4 ∧ False) ∨ (p6 ∨ p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((p0 ∨ p5) ∨ (p6 ∨ True)) := by
      apply Or.inr
      apply Or.inr
      apply True.intro
    let assump_9 := assump_2 assump_13
    apply False.elim assump_9


variable (p2 p0 p5 p7 p4 p6 : Prop)
theorem file49_45421 : ((((((p6 ∧ p7) → (p4 ∨ p5)) → False) ∧ (((p2 ∧ p0) → False) ∨ ((p4 ∧ p2) → (p4 → False)))) ∧ ((((p5 ∨ p7) ∨ (p0 → False)) → False) ∧ (((p2 → False) → (p4 → False)) ∧ ((p4 → p4) → False)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case inl assump_12 =>
        cases assump_7
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            have assump_52 : (p4 → p4) := by
              intro assump_27
              exact assump_27
            let assump_26 := assump_21 assump_52
            apply False.elim assump_26
      case inr assump_13 =>
        cases assump_7
        case intro assump_35 assump_36 =>
          cases assump_36
          case intro assump_39 assump_40 =>
            have assump_53 : (p4 → p4) := by
              intro assump_46
              exact assump_46
            let assump_45 := assump_40 assump_53
            apply False.elim assump_45


variable (p1 p3 p6 : Prop)
theorem file49_46532 : ((((((p6 → False) → (True ∨ p3)) → ((True ∨ p1) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p6 → False) → (True ∨ p3)) → ((True ∨ p1) → False)) → False) := by
    intro assump_5
    have assump_20 : ((p6 → False) → (True ∨ p3)) := by
      intro assump_9
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_20
    have assump_21 : (True ∨ p1) := by
      apply Or.inl
      apply True.intro
    let assump_12 := assump_8 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p3 p2 p4 p5 p6 p0 p7 : Prop)
theorem file49_47187 : (((((p5 ∨ p0) → (p3 → p5)) ∧ ((p6 ∨ p6) ∨ (p0 ∧ p4))) → (((p5 ∧ False) → (p3 ∧ p5)) → ((True → False) → (p5 ∧ p5)))) ∨ ((((p2 ∧ p7) → False) → ((p6 → p4) ∧ (p4 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case inl assump_12 =>
      cases assump_12
      case inl assump_14 =>
        have assump_94 : True := by
          apply True.intro
        let assump_21 := assump_3 assump_94
        apply False.elim assump_21
      case inr assump_15 =>
        have assump_95 : True := by
          apply True.intro
        let assump_30 := assump_3 assump_95
        apply False.elim assump_30
    case inr assump_13 =>
      cases assump_13
      case intro assump_34 assump_35 =>
        have assump_96 : True := by
          apply True.intro
        let assump_45 := assump_3 assump_96
        apply False.elim assump_45
  cases assump_1
  case intro assump_53 assump_54 =>
    cases assump_54
    case inl assump_57 =>
      cases assump_57
      case inl assump_59 =>
        have assump_97 : True := by
          apply True.intro
        let assump_66 := assump_3 assump_97
        apply False.elim assump_66
      case inr assump_60 =>
        have assump_98 : True := by
          apply True.intro
        let assump_75 := assump_3 assump_98
        apply False.elim assump_75
    case inr assump_58 =>
      cases assump_58
      case intro assump_79 assump_80 =>
        have assump_99 : True := by
          apply True.intro
        let assump_90 := assump_3 assump_99
        apply False.elim assump_90


variable (p2 p6 p0 p7 p3 p5 : Prop)
theorem file49_48897 : (((((p2 ∨ p0) ∧ (p7 → False)) → ((True → False) → False)) ∧ (((p7 ∧ p7) → (p3 ∨ p0)) → False)) → ((((p6 → False) → (p5 → False)) → ((p3 ∧ p5) → False)) → (((p7 → False) ∧ (False ∨ p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      apply False.elim assump_8
    case inr assump_9 =>
      cases assump_1
      case intro assump_16 assump_17 =>
        have assump_33 : ((p7 ∧ p7) → (p3 ∨ p0)) := by
          intro assump_23
          cases assump_23
          case intro assump_24 assump_25 =>
            apply Or.inr
            exact assump_9
        let assump_22 := assump_17 assump_33
        apply False.elim assump_22


variable (p3 p0 p5 p2 : Prop)
theorem file49_49700 : ((((((p2 → p2) → (False ∨ p3)) → False) → (((p5 ∧ p5) → (False → False)) ∨ ((True ∧ p0) ∨ (p3 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 → p2) → (False ∨ p3)) → False) → (((p5 ∧ p5) → (False → False)) ∨ ((True ∧ p0) ∨ (p3 ∨ p5)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p2 p6 p0 p1 p5 p7 p3 : Prop)
theorem file49_50205 : (((((p3 ∧ p5) → False) ∧ ((p5 → False) ∧ (p4 ∧ p6))) → (((p5 → False) ∨ (p4 ∨ p0)) → ((p7 → p6) ∨ (p3 ∨ p5)))) ∨ ((((True ∨ p3) → False) → ((p2 ∨ p7) ∧ (p5 → p5))) → (((p4 → p3) ∨ (p7 → p1)) → ((p0 → False) → (p1 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply Or.inl
          intro assump_21
          exact assump_16
  case inr assump_4 =>
    cases assump_4
    case inl assump_24 =>
      cases assump_1
      case intro assump_28 assump_29 =>
        cases assump_29
        case intro assump_32 assump_33 =>
          cases assump_33
          case intro assump_36 assump_37 =>
            apply Or.inl
            intro assump_42
            exact assump_37
    case inr assump_25 =>
      cases assump_1
      case intro assump_47 assump_48 =>
        cases assump_48
        case intro assump_51 assump_52 =>
          cases assump_52
          case intro assump_55 assump_56 =>
            apply Or.inl
            intro assump_61
            exact assump_56


variable (p7 p3 : Prop)
theorem file49_51478 : (((((p3 → False) → False) ∨ ((False ∧ p3) ∧ (False ∨ p3))) ∧ (((p7 → p7) ∧ (False → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_26 : ((p7 → p7) ∧ (False → False)) := by
        apply And.intro
        intro assump_11
        exact assump_11
        intro assump_14
        apply False.elim assump_14
      let assump_10 := assump_3 assump_26
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          apply False.elim assump_22


variable (p6 p7 p0 p3 p5 p4 p2 : Prop)
theorem file49_52224 : (((((p2 ∨ p5) ∨ (p0 → False)) → False) → (((p3 → p5) → False) → ((p6 → False) → (p3 → True)))) ∨ ((((p6 ∨ p7) ∨ (p2 ∧ p4)) → ((p4 → False) ∨ (p0 ∧ p2))) ∨ (((p2 ∨ False) ∧ (p0 ∨ p5)) ∨ ((p7 ∨ p0) ∨ (p5 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply True.intro


variable (p5 p6 p4 p2 p0 : Prop)
theorem file49_52604 : ((((((p4 ∨ p2) ∧ (p5 → p4)) ∨ ((p4 → p6) ∨ (True → False))) ∨ (((p0 → p5) ∧ (p2 → p0)) ∨ ((p5 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p4 ∨ p2) ∧ (p5 → p4)) ∨ ((p4 → p6) ∨ (True → False))) ∨ (((p0 → p5) ∧ (p2 → p0)) ∨ ((p5 ∧ False) → False))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    intro assump_5
    have assump_20 : ((((p4 ∨ p2) ∧ (p5 → p4)) ∨ ((p4 → p6) ∨ (True → False))) ∨ (((p0 → p5) ∧ (p2 → p0)) ∨ ((p5 ∧ False) → False))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      apply Or.inl
      exact assump_5
      intro assump_10
      exact assump_5
    let assump_9 := assump_1 assump_20
    apply False.elim assump_9
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p1 p7 p3 p6 : Prop)
theorem file49_53439 : ((((((p2 ∨ p1) → False) → False) → False) ∧ ((((p3 → False) → False) → False) ∧ (((p3 ∧ p7) ∧ (False ∧ p6)) ∧ ((p6 → p6) → (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              apply False.elim assump_20


variable (p6 p3 p0 p1 p2 p7 p4 : Prop)
theorem file49_54094 : (((((p7 ∧ False) ∧ (True ∨ p4)) → False) → (((p0 ∨ True) ∨ (p1 → True)) ∧ ((p3 ∨ p7) → (False → p6)))) ∨ ((((p3 ∨ p6) ∧ (p4 ∧ p2)) ∧ ((False ∧ p6) → False)) → (((p4 → p1) ∨ (p7 ∧ p3)) ∨ ((p6 ∧ p1) → (True ∧ True))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inl
  apply Or.inr
  apply True.intro
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p6 p2 p3 p1 p7 p4 : Prop)
theorem file49_54538 : (((((p4 → False) → False) ∨ ((False ∧ p4) ∧ (p2 → p6))) → (((True → False) → False) ∨ ((p7 ∨ p2) ∧ (True ∧ p7)))) ∨ ((((p2 ∧ True) ∧ (p3 → p2)) ∧ ((p1 ∧ p2) → False)) → (((p7 → p4) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_9 := assump_6 assump_19
    apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_15


variable (p2 p5 p7 p3 p0 : Prop)
theorem file49_55211 : (((((False ∧ p5) → False) → ((p5 ∨ p3) → False)) ∧ (((True ∨ p2) ∨ (p7 ∧ p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((True ∨ p2) ∨ (p7 ∧ p0)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p1 p5 p7 p3 p6 p2 p0 : Prop)
theorem file49_55628 : (((((p0 → p0) → False) ∧ ((p5 ∨ p3) ∨ (p2 → False))) → (((True → False) ∨ (True → p5)) ∨ ((True ∨ p3) ∧ (p6 → p0)))) ∨ ((((p2 → False) → (p5 → False)) ∨ ((p5 ∨ p2) → (p7 → False))) → (((p2 → False) → False) ∨ ((p1 ∧ p5) ∧ (False → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        apply Or.inl
        intro assump_12
        have assump_49 : (p0 → p0) := by
          intro assump_17
          exact assump_17
        let assump_16 := assump_2 assump_49
        apply False.elim assump_16
      case inr assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_25
        have assump_50 : (p0 → p0) := by
          intro assump_30
          exact assump_30
        let assump_29 := assump_2 assump_50
        apply False.elim assump_29
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_38
      have assump_51 : (p0 → p0) := by
        intro assump_43
        exact assump_43
      let assump_42 := assump_2 assump_51
      apply False.elim assump_42


variable (p1 p2 p3 p5 : Prop)
theorem file49_56855 : ((((((p3 ∧ p2) → (True ∨ p5)) → False) → (((p1 → False) ∧ (p5 ∧ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p3 ∧ p2) → (True ∨ p5)) → False) → (((p1 → False) ∧ (p5 ∧ p5)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_34 : ((p3 ∧ p2) → (True ∨ p5)) := by
          intro assump_20
          cases assump_20
          case intro assump_21 assump_22 =>
            apply Or.inl
            apply True.intro
        let assump_19 := assump_5 assump_34
        apply False.elim assump_19
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p4 p7 p1 p5 p6 : Prop)
theorem file49_57639 : ((((((False ∧ p4) → False) → ((False → False) ∨ (p5 → False))) ∨ (((p7 → p5) ∧ (p7 → p6)) → ((p1 ∨ p4) → False))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((False ∧ p4) → False) → ((False → False) ∨ (p5 → False))) ∨ (((p7 → p5) ∧ (p7 → p6)) → ((p1 ∨ p4) → False))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p1 p5 p3 : Prop)
theorem file49_58152 : ((((((p3 ∧ False) → False) ∨ ((True → p1) → False)) → False) ∧ ((((p1 → False) ∨ (p5 ∧ p2)) → ((True ∧ True) ∨ (True ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p1 → False) ∨ (p5 ∧ p2)) → ((True ∧ True) ∨ (True ∨ p3))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        apply And.intro
        apply True.intro
        apply True.intro
      case inr assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply Or.inl
          apply And.intro
          apply True.intro
          apply True.intro
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p1 p7 p3 p5 p0 p2 p4 p6 : Prop)
theorem file49_58955 : ((((((p7 → p3) ∧ (True → False)) ∧ ((p0 ∧ p1) → False)) ∧ (((False ∨ p7) → False) ∧ ((p2 → p7) ∨ (p2 ∧ p5)))) ∧ ((((p2 → p6) ∧ (p4 → False)) ∨ ((p2 → p2) → False)) ∧ (((p7 ∧ p6) ∧ (p5 ∨ True)) → False))) → False) := by
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
            cases assump_17
            case inl assump_20 =>
              cases assump_3
              case intro assump_24 assump_25 =>
                cases assump_24
                case inl assump_26 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    have assump_100 : True := by
                      apply True.intro
                    let assump_42 := assump_9 assump_100
                    apply False.elim assump_42
                case inr assump_27 =>
                  have assump_101 : (p2 → p2) := by
                    intro assump_52
                    exact assump_52
                  let assump_51 := assump_27 assump_101
                  apply False.elim assump_51
            case inr assump_21 =>
              cases assump_21
              case intro assump_58 assump_59 =>
                cases assump_3
                case intro assump_64 assump_65 =>
                  cases assump_64
                  case inl assump_66 =>
                    cases assump_66
                    case intro assump_68 assump_69 =>
                      have assump_102 : True := by
                        apply True.intro
                      let assump_84 := assump_9 assump_102
                      apply False.elim assump_84
                  case inr assump_67 =>
                    have assump_103 : (p2 → p2) := by
                      intro assump_94
                      exact assump_94
                    let assump_93 := assump_67 assump_103
                    apply False.elim assump_93


variable (p5 p6 p1 p0 p2 : Prop)
theorem file49_61127 : (((((p1 → False) ∧ (False ∧ p6)) → False) ∧ (((False → p0) ∨ (p5 ∧ p6)) ∨ ((p6 ∧ p2) → False))) ∨ ((((p0 → False) ∧ (p2 → p6)) → False) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  apply Or.inl
  apply Or.inl
  intro assump_10
  apply False.elim assump_10


variable (p1 p7 p3 p4 p2 p6 p5 p0 : Prop)
theorem file49_61610 : ((((((False → p2) ∧ (True ∨ p5)) → ((p3 → False) ∨ (p5 ∨ False))) ∧ (((p3 ∧ p4) ∧ (p5 → False)) ∧ ((True ∨ p0) → (p1 → False)))) ∧ ((((p0 → p5) → (p1 → False)) → False) ∧ (((p5 → p1) ∧ (True ∨ p6)) ∧ ((p1 ∧ p7) ∧ (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_22 assump_23 =>
              cases assump_23
              case intro assump_26 assump_27 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  cases assump_29
                  case inl assump_32 =>
                    cases assump_27
                    case intro assump_36 assump_37 =>
                      cases assump_36
                      case intro assump_38 assump_39 =>
                        have assump_66 : p1 := by
                          exact assump_38
                        let assump_46 := assump_37 assump_66
                        apply False.elim assump_46
                  case inr assump_33 =>
                    cases assump_27
                    case intro assump_52 assump_53 =>
                      cases assump_52
                      case intro assump_54 assump_55 =>
                        have assump_67 : p1 := by
                          exact assump_54
                        let assump_62 := assump_53 assump_67
                        apply False.elim assump_62


variable (p7 p2 p3 p5 p6 : Prop)
theorem file49_63352 : (((((p3 → False) ∧ (True → False)) ∧ ((p6 ∨ p3) ∧ (p5 ∧ p2))) → False) ∨ ((((p2 → False) → False) → False) ∧ (((p7 ∨ p7) ∧ (p3 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            have assump_44 : True := by
              apply True.intro
            let assump_25 := assump_5 assump_44
            apply False.elim assump_25
        case inr assump_13 =>
          cases assump_11
          case intro assump_31 assump_32 =>
            have assump_45 : True := by
              apply True.intro
            let assump_40 := assump_5 assump_45
            apply False.elim assump_40


variable (p1 p0 p4 p6 p3 : Prop)
theorem file49_64302 : ((((((p4 ∧ p1) → False) ∨ ((p3 → True) → False)) ∨ (((p0 ∧ p0) → (p6 → False)) → False)) ∧ ((((True ∨ p0) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_53 : (((True ∨ p0) → False) → False) := by
          intro assump_13
          have assump_54 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_16 := assump_13 assump_54
          apply False.elim assump_16
        let assump_12 := assump_3 assump_53
        apply False.elim assump_12
      case inr assump_7 =>
        have assump_55 : (((True ∨ p0) → False) → False) := by
          intro assump_28
          have assump_56 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_31 := assump_28 assump_56
          apply False.elim assump_31
        let assump_27 := assump_3 assump_55
        apply False.elim assump_27
    case inr assump_5 =>
      have assump_57 : (((True ∨ p0) → False) → False) := by
        intro assump_43
        have assump_58 : (True ∨ p0) := by
          apply Or.inl
          apply True.intro
        let assump_46 := assump_43 assump_58
        apply False.elim assump_46
      let assump_42 := assump_3 assump_57
      apply False.elim assump_42


variable (p2 p3 p0 p1 p7 p6 p4 p5 : Prop)
theorem file49_65764 : ((((((p3 → p4) ∨ (p6 ∨ p0)) → ((True → False) ∧ (p5 ∧ False))) ∨ (((p2 ∧ True) ∧ (p2 ∧ p4)) → ((p1 ∧ p2) ∨ (False ∨ p7)))) ∧ ((((p1 → False) → (False → False)) → False) ∧ (((False ∧ True) → (p2 → False)) → False))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_9
      case intro assump_14 assump_15 =>
        have assump_52 : ((False ∧ True) → (p2 → False)) := by
          intro assump_21
          intro assump_22
          cases assump_21
          case intro assump_25 assump_26 =>
            apply False.elim assump_25
        let assump_20 := assump_15 assump_52
        apply False.elim assump_20
    case inr assump_11 =>
      cases assump_9
      case intro assump_34 assump_35 =>
        have assump_53 : ((False ∧ True) → (p2 → False)) := by
          intro assump_41
          intro assump_42
          cases assump_41
          case intro assump_45 assump_46 =>
            apply False.elim assump_45
        let assump_40 := assump_35 assump_53
        apply False.elim assump_40


variable (p4 p7 p6 p5 p2 p3 p1 p0 : Prop)
theorem file49_66929 : (((((p4 → p7) → False) → ((p4 ∨ True) ∨ (False → False))) → False) → ((((p0 → p1) → (False → False)) ∧ ((False → True) ∨ (p6 ∧ p6))) ∧ (((p2 → p7) → (p6 → p4)) ∨ ((p3 ∧ p5) ∧ (p4 ∧ False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  apply False.elim assump_3
  apply Or.inl
  intro assump_8
  apply True.intro
  apply Or.inl
  intro assump_11
  intro assump_12
  have assump_26 : (((p4 → p7) → False) → ((p4 ∨ True) ∨ (False → False))) := by
    intro assump_20
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_19 := assump_1 assump_26
  apply False.elim assump_19


variable (p3 p1 p7 p5 p0 p6 p4 : Prop)
theorem file49_67630 : ((((((p0 ∨ p1) → False) ∨ ((p4 → False) ∨ (p0 → False))) ∧ (((False ∧ p3) → False) → False)) ∧ ((((p1 ∧ False) ∨ (p1 → p7)) ∨ ((p5 ∧ p7) ∨ (p6 → p6))) ∨ (((p3 ∧ p0) ∨ (p0 → False)) ∧ ((True ∨ p0) ∨ (p4 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                apply False.elim assump_19
            case inr assump_17 =>
              have assump_496 : ((False ∧ p3) → False) := by
                intro assump_28
                cases assump_28
                case intro assump_29 assump_30 =>
                  apply False.elim assump_29
              let assump_27 := assump_5 assump_496
              apply False.elim assump_27
          case inr assump_15 =>
            cases assump_15
            case inl assump_36 =>
              cases assump_36
              case intro assump_38 assump_39 =>
                have assump_497 : ((False ∧ p3) → False) := by
                  intro assump_47
                  cases assump_47
                  case intro assump_48 assump_49 =>
                    apply False.elim assump_48
                let assump_46 := assump_5 assump_497
                apply False.elim assump_46
            case inr assump_37 =>
              have assump_498 : ((False ∧ p3) → False) := by
                intro assump_59
                cases assump_59
                case intro assump_60 assump_61 =>
                  apply False.elim assump_60
              let assump_58 := assump_5 assump_498
              apply False.elim assump_58
        case inr assump_13 =>
          cases assump_13
          case intro assump_67 assump_68 =>
            cases assump_67
            case inl assump_69 =>
              cases assump_69
              case intro assump_71 assump_72 =>
                cases assump_68
                case inl assump_77 =>
                  cases assump_77
                  case inl assump_79 =>
                    have assump_499 : ((False ∧ p3) → False) := by
                      intro assump_86
                      cases assump_86
                      case intro assump_87 assump_88 =>
                        apply False.elim assump_87
                    let assump_85 := assump_5 assump_499
                    apply False.elim assump_85
                  case inr assump_80 =>
                    have assump_500 : ((False ∧ p3) → False) := by
                      intro assump_100
                      cases assump_100
                      case intro assump_101 assump_102 =>
                        apply False.elim assump_101
                    let assump_99 := assump_5 assump_500
                    apply False.elim assump_99
                case inr assump_78 =>
                  cases assump_78
                  case intro assump_108 assump_109 =>
                    have assump_501 : ((False ∧ p3) → False) := by
                      intro assump_119
                      cases assump_119
                      case intro assump_120 assump_121 =>
                        apply False.elim assump_120
                    let assump_118 := assump_5 assump_501
                    apply False.elim assump_118
            case inr assump_70 =>
              cases assump_68
              case inl assump_129 =>
                cases assump_129
                case inl assump_131 =>
                  have assump_502 : ((False ∧ p3) → False) := by
                    intro assump_137
                    cases assump_137
                    case intro assump_138 assump_139 =>
                      apply False.elim assump_138
                  let assump_136 := assump_5 assump_502
                  apply False.elim assump_136
                case inr assump_132 =>
                  have assump_503 : p0 := by
                    exact assump_132
                  let assump_148 := assump_70 assump_503
                  apply False.elim assump_148
              case inr assump_130 =>
                cases assump_130
                case intro assump_152 assump_153 =>
                  have assump_504 : ((False ∧ p3) → False) := by
                    intro assump_162
                    cases assump_162
                    case intro assump_163 assump_164 =>
                      apply False.elim assump_163
                  let assump_161 := assump_5 assump_504
                  apply False.elim assump_161
      case inr assump_7 =>
        cases assump_7
        case inl assump_170 =>
          cases assump_3
          case inl assump_176 =>
            cases assump_176
            case inl assump_178 =>
              cases assump_178
              case inl assump_180 =>
                cases assump_180
                case intro assump_182 assump_183 =>
                  apply False.elim assump_183
              case inr assump_181 =>
                have assump_505 : ((False ∧ p3) → False) := by
                  intro assump_192
                  cases assump_192
                  case intro assump_193 assump_194 =>
                    apply False.elim assump_193
                let assump_191 := assump_5 assump_505
                apply False.elim assump_191
            case inr assump_179 =>
              cases assump_179
              case inl assump_200 =>
                cases assump_200
                case intro assump_202 assump_203 =>
                  have assump_506 : ((False ∧ p3) → False) := by
                    intro assump_211
                    cases assump_211
                    case intro assump_212 assump_213 =>
                      apply False.elim assump_212
                  let assump_210 := assump_5 assump_506
                  apply False.elim assump_210
              case inr assump_201 =>
                have assump_507 : ((False ∧ p3) → False) := by
                  intro assump_223
                  cases assump_223
                  case intro assump_224 assump_225 =>
                    apply False.elim assump_224
                let assump_222 := assump_5 assump_507
                apply False.elim assump_222
          case inr assump_177 =>
            cases assump_177
            case intro assump_231 assump_232 =>
              cases assump_231
              case inl assump_233 =>
                cases assump_233
                case intro assump_235 assump_236 =>
                  cases assump_232
                  case inl assump_241 =>
                    cases assump_241
                    case inl assump_243 =>
                      have assump_508 : ((False ∧ p3) → False) := by
                        intro assump_250
                        cases assump_250
                        case intro assump_251 assump_252 =>
                          apply False.elim assump_251
                      let assump_249 := assump_5 assump_508
                      apply False.elim assump_249
                    case inr assump_244 =>
                      have assump_509 : ((False ∧ p3) → False) := by
                        intro assump_264
                        cases assump_264
                        case intro assump_265 assump_266 =>
                          apply False.elim assump_265
                      let assump_263 := assump_5 assump_509
                      apply False.elim assump_263
                  case inr assump_242 =>
                    cases assump_242
                    case intro assump_272 assump_273 =>
                      have assump_510 : ((False ∧ p3) → False) := by
                        intro assump_283
                        cases assump_283
                        case intro assump_284 assump_285 =>
                          apply False.elim assump_284
                      let assump_282 := assump_5 assump_510
                      apply False.elim assump_282
              case inr assump_234 =>
                cases assump_232
                case inl assump_293 =>
                  cases assump_293
                  case inl assump_295 =>
                    have assump_511 : ((False ∧ p3) → False) := by
                      intro assump_301
                      cases assump_301
                      case intro assump_302 assump_303 =>
                        apply False.elim assump_302
                    let assump_300 := assump_5 assump_511
                    apply False.elim assump_300
                  case inr assump_296 =>
                    have assump_512 : p0 := by
                      exact assump_296
                    let assump_312 := assump_234 assump_512
                    apply False.elim assump_312
                case inr assump_294 =>
                  cases assump_294
                  case intro assump_316 assump_317 =>
                    have assump_513 : ((False ∧ p3) → False) := by
                      intro assump_326
                      cases assump_326
                      case intro assump_327 assump_328 =>
                        apply False.elim assump_327
                    let assump_325 := assump_5 assump_513
                    apply False.elim assump_325
        case inr assump_171 =>
          cases assump_3
          case inl assump_338 =>
            cases assump_338
            case inl assump_340 =>
              cases assump_340
              case inl assump_342 =>
                cases assump_342
                case intro assump_344 assump_345 =>
                  apply False.elim assump_345
              case inr assump_343 =>
                have assump_514 : ((False ∧ p3) → False) := by
                  intro assump_354
                  cases assump_354
                  case intro assump_355 assump_356 =>
                    apply False.elim assump_355
                let assump_353 := assump_5 assump_514
                apply False.elim assump_353
            case inr assump_341 =>
              cases assump_341
              case inl assump_362 =>
                cases assump_362
                case intro assump_364 assump_365 =>
                  have assump_515 : ((False ∧ p3) → False) := by
                    intro assump_373
                    cases assump_373
                    case intro assump_374 assump_375 =>
                      apply False.elim assump_374
                  let assump_372 := assump_5 assump_515
                  apply False.elim assump_372
              case inr assump_363 =>
                have assump_516 : ((False ∧ p3) → False) := by
                  intro assump_385
                  cases assump_385
                  case intro assump_386 assump_387 =>
                    apply False.elim assump_386
                let assump_384 := assump_5 assump_516
                apply False.elim assump_384
          case inr assump_339 =>
            cases assump_339
            case intro assump_393 assump_394 =>
              cases assump_393
              case inl assump_395 =>
                cases assump_395
                case intro assump_397 assump_398 =>
                  cases assump_394
                  case inl assump_403 =>
                    cases assump_403
                    case inl assump_405 =>
                      have assump_517 : ((False ∧ p3) → False) := by
                        intro assump_412
                        cases assump_412
                        case intro assump_413 assump_414 =>
                          apply False.elim assump_413
                      let assump_411 := assump_5 assump_517
                      apply False.elim assump_411
                    case inr assump_406 =>
                      have assump_518 : ((False ∧ p3) → False) := by
                        intro assump_426
                        cases assump_426
                        case intro assump_427 assump_428 =>
                          apply False.elim assump_427
                      let assump_425 := assump_5 assump_518
                      apply False.elim assump_425
                  case inr assump_404 =>
                    cases assump_404
                    case intro assump_434 assump_435 =>
                      have assump_519 : ((False ∧ p3) → False) := by
                        intro assump_445
                        cases assump_445
                        case intro assump_446 assump_447 =>
                          apply False.elim assump_446
                      let assump_444 := assump_5 assump_519
                      apply False.elim assump_444
              case inr assump_396 =>
                cases assump_394
                case inl assump_455 =>
                  cases assump_455
                  case inl assump_457 =>
                    have assump_520 : ((False ∧ p3) → False) := by
                      intro assump_463
                      cases assump_463
                      case intro assump_464 assump_465 =>
                        apply False.elim assump_464
                    let assump_462 := assump_5 assump_520
                    apply False.elim assump_462
                  case inr assump_458 =>
                    have assump_521 : p0 := by
                      exact assump_458
                    let assump_474 := assump_396 assump_521
                    apply False.elim assump_474
                case inr assump_456 =>
                  cases assump_456
                  case intro assump_478 assump_479 =>
                    have assump_522 : ((False ∧ p3) → False) := by
                      intro assump_488
                      cases assump_488
                      case intro assump_489 assump_490 =>
                        apply False.elim assump_489
                    let assump_487 := assump_5 assump_522
                    apply False.elim assump_487


variable (p5 p4 p7 p3 p6 p1 p2 p0 : Prop)
theorem file49_81701 : (((((False → p4) → (p7 ∨ False)) → False) → (((p2 ∨ p6) → (False → False)) ∧ ((p4 → False) ∨ (p0 ∨ p3)))) → ((((p3 ∧ p4) ∨ (p2 ∧ p3)) ∧ ((p1 → p4) ∧ (p6 → False))) → (((p1 → p6) ∨ (p5 → p7)) → ((p4 → False) → (p0 → p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_3
  case inl assump_10 =>
    cases assump_2
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_15
          case intro assump_24 assump_25 =>
            exact assump_18
      case inr assump_17 =>
        cases assump_17
        case intro assump_32 assump_33 =>
          cases assump_15
          case intro assump_38 assump_39 =>
            exact assump_33
  case inr assump_11 =>
    cases assump_2
    case intro assump_48 assump_49 =>
      cases assump_48
      case inl assump_50 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          cases assump_49
          case intro assump_58 assump_59 =>
            exact assump_52
      case inr assump_51 =>
        cases assump_51
        case intro assump_66 assump_67 =>
          cases assump_49
          case intro assump_72 assump_73 =>
            exact assump_67


variable (p7 p2 p0 p6 p1 p5 p3 : Prop)
theorem file49_83069 : (((((p3 ∨ p3) ∨ (p7 → False)) ∧ ((p6 ∨ False) ∧ (p6 ∧ False))) ∧ (((p1 → False) → (p7 ∧ p1)) → ((p5 → p5) → (p6 ∧ p5)))) → ((((p2 ∧ p6) ∧ (p0 → False)) ∨ ((p5 → p5) → False)) ∧ (((p7 ∧ p0) → (p1 ∧ True)) → False))) := by
  intro assump_1
  apply And.intro
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
            cases assump_12
            case inl assump_14 =>
              cases assump_13
              case intro assump_18 assump_19 =>
                apply False.elim assump_19
            case inr assump_15 =>
              apply False.elim assump_15
        case inr assump_9 =>
          cases assump_5
          case intro assump_28 assump_29 =>
            cases assump_28
            case inl assump_30 =>
              cases assump_29
              case intro assump_34 assump_35 =>
                apply False.elim assump_35
            case inr assump_31 =>
              apply False.elim assump_31
      case inr assump_7 =>
        cases assump_5
        case intro assump_44 assump_45 =>
          cases assump_44
          case inl assump_46 =>
            cases assump_45
            case intro assump_50 assump_51 =>
              apply False.elim assump_51
          case inr assump_47 =>
            apply False.elim assump_47
  intro assump_58
  cases assump_1
  case intro assump_61 assump_62 =>
    cases assump_61
    case intro assump_63 assump_64 =>
      cases assump_63
      case inl assump_65 =>
        cases assump_65
        case inl assump_67 =>
          cases assump_64
          case intro assump_71 assump_72 =>
            cases assump_71
            case inl assump_73 =>
              cases assump_72
              case intro assump_77 assump_78 =>
                apply False.elim assump_78
            case inr assump_74 =>
              apply False.elim assump_74
        case inr assump_68 =>
          cases assump_64
          case intro assump_87 assump_88 =>
            cases assump_87
            case inl assump_89 =>
              cases assump_88
              case intro assump_93 assump_94 =>
                apply False.elim assump_94
            case inr assump_90 =>
              apply False.elim assump_90
      case inr assump_66 =>
        cases assump_64
        case intro assump_103 assump_104 =>
          cases assump_103
          case inl assump_105 =>
            cases assump_104
            case intro assump_109 assump_110 =>
              apply False.elim assump_110
          case inr assump_106 =>
            apply False.elim assump_106


variable (p3 p7 p5 p6 p4 p1 p2 : Prop)
theorem file49_85880 : (((((p6 → False) ∨ (p6 ∧ p3)) → ((False ∨ True) ∨ (True ∨ p2))) ∨ (((p3 → False) → False) ∨ ((p7 → p5) ∧ (True → False)))) ∨ ((((True → False) ∧ (p5 ∧ p3)) ∧ ((True ∨ p4) ∨ (p5 → p2))) ∨ (((True → p1) ∨ (True → p2)) ∧ ((p4 → p5) ∨ (False ∨ p6))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inr
      apply True.intro


variable (p0 p2 p6 p7 p4 p1 p3 : Prop)
theorem file49_86478 : (((((p3 ∨ p3) ∧ (False → False)) → ((False → p4) → (p7 ∨ p3))) → (((p4 → False) → (p1 ∨ p0)) → False)) → ((((p4 ∨ p2) ∨ (p6 ∧ p6)) ∨ ((p1 ∨ p4) ∨ (p2 ∨ p1))) → (((False → False) ∧ (p0 ∨ p3)) ∨ ((p1 → p4) ∨ (p0 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        apply Or.inr
        apply Or.inl
        intro assump_16
        exact assump_7
      case inr assump_8 =>
        apply Or.inr
        apply Or.inl
        intro assump_26
        have assump_214 : (((p3 ∨ p3) ∧ (False → False)) → ((False → p4) → (p7 ∨ p3))) := by
          intro assump_31
          intro assump_32
          cases assump_31
          case intro assump_35 assump_36 =>
            cases assump_35
            case inl assump_37 =>
              apply Or.inr
              exact assump_37
            case inr assump_38 =>
              apply Or.inr
              exact assump_38
        let assump_30 := assump_1 assump_214
        have assump_215 : ((p4 → False) → (p1 ∨ p0)) := by
          intro assump_48
          apply Or.inl
          exact assump_26
        let assump_47 := assump_30 assump_215
        apply False.elim assump_47
    case inr assump_6 =>
      cases assump_6
      case intro assump_54 assump_55 =>
        apply Or.inr
        apply Or.inl
        intro assump_65
        have assump_216 : (((p3 ∨ p3) ∧ (False → False)) → ((False → p4) → (p7 ∨ p3))) := by
          intro assump_70
          intro assump_71
          cases assump_70
          case intro assump_74 assump_75 =>
            cases assump_74
            case inl assump_76 =>
              apply Or.inr
              exact assump_76
            case inr assump_77 =>
              apply Or.inr
              exact assump_77
        let assump_69 := assump_1 assump_216
        have assump_217 : ((p4 → False) → (p1 ∨ p0)) := by
          intro assump_87
          apply Or.inl
          exact assump_65
        let assump_86 := assump_69 assump_217
        apply False.elim assump_86
  case inr assump_4 =>
    cases assump_4
    case inl assump_93 =>
      cases assump_93
      case inl assump_95 =>
        apply Or.inr
        apply Or.inl
        intro assump_104
        have assump_218 : (((p3 ∨ p3) ∧ (False → False)) → ((False → p4) → (p7 ∨ p3))) := by
          intro assump_109
          intro assump_110
          cases assump_109
          case intro assump_113 assump_114 =>
            cases assump_113
            case inl assump_115 =>
              apply Or.inr
              exact assump_115
            case inr assump_116 =>
              apply Or.inr
              exact assump_116
        let assump_108 := assump_1 assump_218
        have assump_219 : ((p4 → False) → (p1 ∨ p0)) := by
          intro assump_126
          apply Or.inl
          exact assump_104
        let assump_125 := assump_108 assump_219
        apply False.elim assump_125
      case inr assump_96 =>
        apply Or.inr
        apply Or.inl
        intro assump_139
        exact assump_96
    case inr assump_94 =>
      cases assump_94
      case inl assump_142 =>
        apply Or.inr
        apply Or.inl
        intro assump_151
        have assump_220 : (((p3 ∨ p3) ∧ (False → False)) → ((False → p4) → (p7 ∨ p3))) := by
          intro assump_156
          intro assump_157
          cases assump_156
          case intro assump_160 assump_161 =>
            cases assump_160
            case inl assump_162 =>
              apply Or.inr
              exact assump_162
            case inr assump_163 =>
              apply Or.inr
              exact assump_163
        let assump_155 := assump_1 assump_220
        have assump_221 : ((p4 → False) → (p1 ∨ p0)) := by
          intro assump_173
          apply Or.inl
          exact assump_151
        let assump_172 := assump_155 assump_221
        apply False.elim assump_172
      case inr assump_143 =>
        apply Or.inr
        apply Or.inl
        intro assump_186
        have assump_222 : (((p3 ∨ p3) ∧ (False → False)) → ((False → p4) → (p7 ∨ p3))) := by
          intro assump_191
          intro assump_192
          cases assump_191
          case intro assump_195 assump_196 =>
            cases assump_195
            case inl assump_197 =>
              apply Or.inr
              exact assump_197
            case inr assump_198 =>
              apply Or.inr
              exact assump_198
        let assump_190 := assump_1 assump_222
        have assump_223 : ((p4 → False) → (p1 ∨ p0)) := by
          intro assump_208
          apply Or.inl
          exact assump_186
        let assump_207 := assump_190 assump_223
        apply False.elim assump_207


variable (p7 p5 p3 p2 p4 p1 : Prop)
theorem file49_91284 : ((((((False ∧ p4) → (p5 → False)) ∨ ((p3 ∨ p4) → False)) ∨ (((p2 → False) → (p7 → p1)) ∨ ((False ∨ p2) → (p4 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False ∧ p4) → (p5 → False)) ∨ ((p3 ∨ p4) → False)) ∨ (((p2 → False) → (p7 → p1)) ∨ ((False ∨ p2) → (p4 ∧ p7)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p1 p2 p0 p3 p5 p4 p7 : Prop)
theorem file49_91872 : ((((((p3 ∧ False) ∧ (p4 ∧ p1)) ∧ ((p0 → p1) ∨ (False ∧ p0))) ∧ (((p3 ∨ p7) → False) → ((p2 ∨ p0) → (p2 → p2)))) ∧ ((((p5 → p4) ∧ (p5 → False)) → ((p1 ∧ False) → False)) ∧ (((p5 → False) → False) ∧ ((p4 → p4) → (p5 ∨ p0))))) → False) := by
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
            apply False.elim assump_11


variable (p2 p6 p7 : Prop)
theorem file49_92515 : ((((((False ∧ p2) → False) ∧ ((p7 ∧ False) → False)) ∨ (((p2 → False) → False) ∧ ((p6 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ p2) → False) ∧ ((p7 ∧ False) → False)) ∨ (((p2 → False) → False) ∧ ((p6 → False) → False))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 p0 p6 p7 p3 p2 p4 : Prop)
theorem file49_93173 : (((((p2 ∨ p7) → False) → ((p4 ∧ p6) → (True ∨ p0))) → False) → ((((p3 ∧ p3) ∧ (p1 → False)) ∧ ((p3 ∧ True) → (p3 ∧ p6))) ∧ (((p7 ∨ p0) ∨ (p2 ∨ p6)) ∧ ((p4 ∨ p0) ∧ (p6 ∧ p6))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  apply And.intro
  have assump_148 : (((p2 ∨ p7) → False) → ((p4 ∧ p6) → (True ∨ p0))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_148
  apply False.elim assump_4
  have assump_149 : (((p2 ∨ p7) → False) → ((p4 ∧ p6) → (True ∨ p0))) := by
    intro assump_21
    intro assump_22
    cases assump_22
    case intro assump_23 assump_24 =>
      apply Or.inl
      apply True.intro
  let assump_20 := assump_1 assump_149
  apply False.elim assump_20
  intro assump_34
  have assump_150 : (((p2 ∨ p7) → False) → ((p4 ∧ p6) → (True ∨ p0))) := by
    intro assump_40
    intro assump_41
    cases assump_41
    case intro assump_42 assump_43 =>
      apply Or.inl
      apply True.intro
  let assump_39 := assump_1 assump_150
  apply False.elim assump_39
  intro assump_53
  apply And.intro
  cases assump_53
  case intro assump_54 assump_55 =>
    exact assump_54
  cases assump_53
  case intro assump_62 assump_63 =>
    have assump_151 : (((p2 ∨ p7) → False) → ((p4 ∧ p6) → (True ∨ p0))) := by
      intro assump_71
      intro assump_72
      cases assump_72
      case intro assump_73 assump_74 =>
        apply Or.inl
        apply True.intro
    let assump_70 := assump_1 assump_151
    apply False.elim assump_70
  apply And.intro
  have assump_152 : (((p2 ∨ p7) → False) → ((p4 ∧ p6) → (True ∨ p0))) := by
    intro assump_87
    intro assump_88
    cases assump_88
    case intro assump_89 assump_90 =>
      apply Or.inl
      apply True.intro
  let assump_86 := assump_1 assump_152
  apply False.elim assump_86
  apply And.intro
  have assump_153 : (((p2 ∨ p7) → False) → ((p4 ∧ p6) → (True ∨ p0))) := by
    intro assump_103
    intro assump_104
    cases assump_104
    case intro assump_105 assump_106 =>
      apply Or.inl
      apply True.intro
  let assump_102 := assump_1 assump_153
  apply False.elim assump_102
  apply And.intro
  have assump_154 : (((p2 ∨ p7) → False) → ((p4 ∧ p6) → (True ∨ p0))) := by
    intro assump_119
    intro assump_120
    cases assump_120
    case intro assump_121 assump_122 =>
      apply Or.inl
      apply True.intro
  let assump_118 := assump_1 assump_154
  apply False.elim assump_118
  have assump_155 : (((p2 ∨ p7) → False) → ((p4 ∧ p6) → (True ∨ p0))) := by
    intro assump_135
    intro assump_136
    cases assump_136
    case intro assump_137 assump_138 =>
      apply Or.inl
      apply True.intro
  let assump_134 := assump_1 assump_155
  apply False.elim assump_134


variable (p4 p6 p5 p2 p0 p7 p3 p1 : Prop)
theorem file49_96051 : (((((False ∨ p1) ∧ (p1 → False)) ∧ ((p3 → False) ∨ (False → False))) → False) ∨ ((((p0 ∧ p6) → False) ∧ ((True → p4) ∨ (p6 → p0))) ∨ (((p4 ∧ p6) ∨ (p2 ∨ p7)) → ((True → False) → (p5 ∧ p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        apply False.elim assump_6
      case inr assump_7 =>
        cases assump_3
        case inl assump_14 =>
          have assump_30 : p1 := by
            exact assump_7
          let assump_19 := assump_5 assump_30
          apply False.elim assump_19
        case inr assump_15 =>
          have assump_31 : p1 := by
            exact assump_7
          let assump_26 := assump_5 assump_31
          apply False.elim assump_26


variable (p3 p4 p1 p2 p0 : Prop)
theorem file49_96928 : (((((p0 ∨ True) ∨ (p2 → p1)) → False) → False) ∨ ((((p1 → False) ∨ (False ∨ p3)) → ((p1 ∨ p0) ∨ (p4 ∧ p3))) ∧ (((p4 → p2) ∧ (True ∨ True)) → ((p2 → True) → False)))) := by
  apply Or.inl
  intro assump_7
  have assump_14 : ((p0 ∨ True) ∨ (p2 → p1)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_10 := assump_7 assump_14
  apply False.elim assump_10


variable (p7 p4 p5 p3 p2 p1 p0 p6 : Prop)
theorem file49_97371 : (((((p7 → True) → False) ∧ ((p3 → False) → (p1 → p6))) ∧ (((p2 ∧ p5) → (p3 ∨ p5)) → ((False → False) → (p6 → p4)))) → ((((p4 ∨ p6) → False) ∧ ((p3 ∧ False) ∧ (p4 → False))) → (((p0 → p0) ∧ (p6 → False)) ∨ ((p7 ∨ p7) ∧ (p0 ∧ True))))) := by
  intro assump_14
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_17
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        apply False.elim assump_23


variable (p5 p1 p4 p0 p3 p7 : Prop)
theorem file49_97916 : (((((p3 → False) → False) → False) → False) → ((((p7 ∧ p4) ∧ (False ∨ p0)) ∨ ((True ∧ p0) ∧ (p5 ∧ p3))) ∨ (((p1 → False) ∨ (p1 ∧ p5)) → ((p7 ∧ False) → (False → p5))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  intro assump_5
  intro assump_6
  apply False.elim assump_6


variable (p3 p5 p1 p2 p7 p6 p0 : Prop)
theorem file49_98265 : (((((p6 ∧ p1) → (p7 ∨ p6)) → ((p2 ∧ p0) ∨ (p0 ∨ True))) → False) → ((((p7 ∨ p5) → (p6 → p3)) ∧ ((p3 → False) ∧ (p5 → p2))) ∨ (((p7 → p2) → (False → False)) ∧ ((p6 → p5) → (p1 → p5))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_54 : (((p6 ∧ p1) → (p7 ∨ p6)) → ((p2 ∧ p0) ∨ (p0 ∨ True))) := by
      intro assump_15
      apply Or.inr
      apply Or.inr
      apply True.intro
    let assump_14 := assump_1 assump_54
    apply False.elim assump_14
  case inr assump_9 =>
    have assump_55 : (((p6 ∧ p1) → (p7 ∨ p6)) → ((p2 ∧ p0) ∨ (p0 ∨ True))) := by
      intro assump_26
      apply Or.inr
      apply Or.inr
      apply True.intro
    let assump_25 := assump_1 assump_55
    apply False.elim assump_25
  apply And.intro
  intro assump_32
  have assump_56 : (((p6 ∧ p1) → (p7 ∨ p6)) → ((p2 ∧ p0) ∨ (p0 ∨ True))) := by
    intro assump_37
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_36 := assump_1 assump_56
  apply False.elim assump_36
  intro assump_43
  have assump_57 : (((p6 ∧ p1) → (p7 ∨ p6)) → ((p2 ∧ p0) ∨ (p0 ∨ True))) := by
    intro assump_48
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_47 := assump_1 assump_57
  apply False.elim assump_47


variable (p2 p6 p1 p7 p0 p4 : Prop)
theorem file49_99629 : (((((p2 → p7) → (p0 → False)) ∧ ((p1 → True) → False)) → (((True ∧ p1) → False) → False)) ∨ ((((p6 ∧ p7) → (p0 ∨ p1)) ∨ ((p2 ∨ False) ∧ (p6 ∨ p4))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_16 : (p1 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_6 assump_16
    apply False.elim assump_11


variable (p7 p6 p2 p3 p4 p1 : Prop)
theorem file49_100108 : ((((((p1 ∧ False) → (p4 ∨ p7)) ∧ ((p2 → p6) ∧ (True → False))) → (((p3 ∨ p6) ∨ (p1 → False)) ∧ ((p7 → False) ∧ (p6 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_72 : ((((p1 ∧ False) → (p4 ∨ p7)) ∧ ((p2 → p6) ∧ (True → False))) → (((p3 ∨ p6) ∨ (p1 → False)) ∧ ((p7 → False) ∧ (p6 ∧ False)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inr
        intro assump_16
        have assump_73 : True := by
          apply True.intro
        let assump_20 := assump_11 assump_73
        apply False.elim assump_20
    apply And.intro
    intro assump_24
    cases assump_5
    case intro assump_27 assump_28 =>
      cases assump_28
      case intro assump_31 assump_32 =>
        have assump_74 : True := by
          apply True.intro
        let assump_37 := assump_32 assump_74
        apply False.elim assump_37
    apply And.intro
    cases assump_5
    case intro assump_41 assump_42 =>
      cases assump_42
      case intro assump_45 assump_46 =>
        have assump_75 : True := by
          apply True.intro
        let assump_51 := assump_46 assump_75
        apply False.elim assump_51
    cases assump_5
    case intro assump_55 assump_56 =>
      cases assump_56
      case intro assump_59 assump_60 =>
        have assump_76 : True := by
          apply True.intro
        let assump_65 := assump_60 assump_76
        apply False.elim assump_65
  let assump_4 := assump_1 assump_72
  apply False.elim assump_4


variable (p7 p0 : Prop)
theorem file49_101728 : (((((p7 → False) ∧ (True → False)) → ((p0 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : (((p7 → False) ∧ (True → False)) → ((p0 → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_23 : True := by
        apply True.intro
      let assump_15 := assump_10 assump_23
      apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p1 p5 p7 p0 p3 p2 : Prop)
theorem file49_102271 : (((((p2 ∧ p4) → (p0 → False)) → False) ∨ (((p5 ∨ p4) ∧ (p2 → False)) → False)) → ((((p2 → True) ∨ (p1 → False)) → False) → (((p7 → p0) → False) → ((p3 ∧ p4) → (True ∨ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_1
    case inl assump_15 =>
      apply Or.inl
      apply True.intro
    case inr assump_16 =>
      apply Or.inl
      apply True.intro


variable (p3 p4 p7 p2 p0 p5 p6 : Prop)
theorem file49_102789 : (((((p4 → False) ∧ (p2 ∧ p7)) ∧ ((p3 → p2) → (p2 ∧ p2))) → (((p4 → False) ∨ (p2 ∧ p3)) ∨ ((p3 ∧ p6) ∨ (p0 → p4)))) ∨ ((((p7 → False) ∨ (p2 ∨ True)) → False) ∧ (((p2 ∧ p5) ∨ (True ∨ p3)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_16
        have assump_33 : p4 := by
          exact assump_16
        let assump_29 := assump_4 assump_33
        apply False.elim assump_29


variable (p0 p1 p5 p2 : Prop)
theorem file49_103448 : ((((((p2 ∨ p0) ∨ (p0 → False)) ∨ ((p2 → False) → False)) ∨ (((p1 → False) → (p5 → False)) ∨ ((p5 ∧ p2) ∧ (True ∧ p5)))) → False) → False) := by
  intro assump_21
  have assump_36 : ((((p2 ∨ p0) ∨ (p0 → False)) ∨ ((p2 → False) → False)) ∨ (((p1 → False) → (p5 → False)) ∨ ((p5 ∧ p2) ∧ (True ∧ p5)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_25
    have assump_37 : ((((p2 ∨ p0) ∨ (p0 → False)) ∨ ((p2 → False) → False)) ∨ (((p1 → False) → (p5 → False)) ∨ ((p5 ∧ p2) ∧ (True ∧ p5)))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact assump_25
    let assump_29 := assump_21 assump_37
    apply False.elim assump_29
  let assump_24 := assump_21 assump_36
  apply False.elim assump_24


variable (p3 : Prop)
theorem file49_104252 : ((((((p3 ∧ False) → False) → False) → False) → False) → False) := by
  intro assump_5
  have assump_26 : ((((p3 ∧ False) → False) → False) → False) := by
    intro assump_9
    have assump_27 : ((p3 ∧ False) → False) := by
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
    let assump_12 := assump_9 assump_27
    apply False.elim assump_12
  let assump_8 := assump_5 assump_26
  apply False.elim assump_8


variable (p5 p0 p4 : Prop)
theorem file49_104781 : (((((p0 ∧ True) → False) ∧ ((p0 → False) → (p5 → False))) ∧ (((False → False) ∨ (p5 ∧ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_19 : ((False → False) ∨ (p5 ∧ p4)) := by
        apply Or.inl
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_3 assump_19
      apply False.elim assump_12


variable (p0 p3 p7 p2 p5 p6 : Prop)
theorem file49_105294 : (((((p5 → p3) → False) ∨ ((False ∧ p2) → (p0 → p7))) → (((True → p2) → (True ∧ p2)) ∨ ((p6 ∧ p2) → False))) ∨ ((((p0 ∧ p0) ∨ (p0 ∨ True)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply And.intro
    apply True.intro
    have assump_18 : True := by
      apply True.intro
    let assump_9 := assump_6 assump_18
    exact assump_9
  case inr assump_3 =>
    apply Or.inl
    intro assump_13
    apply And.intro
    apply True.intro
    have assump_19 : True := by
      apply True.intro
    let assump_16 := assump_13 assump_19
    exact assump_16


variable (p1 p7 p3 p0 p2 p6 p4 : Prop)
theorem file49_105999 : (((((p4 ∧ p1) ∧ (p0 ∧ False)) → ((p6 ∧ p4) ∧ (p3 → p3))) ∧ (((p7 ∨ p2) ∧ (p2 → False)) ∨ ((p6 ∧ p4) ∧ (False ∧ p7)))) ∨ ((((p7 ∧ p6) ∧ (False → False)) ∧ ((p6 → False) ∧ (p2 → False))) → (((p2 ∨ p3) → False) ∨ ((p7 ∧ p0) ∧ (p7 ∨ p1))))) := by
  apply Or.inr
  intro assump_47
  cases assump_47
  case intro assump_48 assump_49 =>
    cases assump_48
    case intro assump_50 assump_51 =>
      cases assump_50
      case intro assump_52 assump_53 =>
        cases assump_49
        case intro assump_60 assump_61 =>
          apply Or.inl
          intro assump_66
          cases assump_66
          case inl assump_67 =>
            have assump_84 : p2 := by
              exact assump_67
            let assump_72 := assump_61 assump_84
            apply False.elim assump_72
          case inr assump_68 =>
            have assump_85 : p6 := by
              exact assump_53
            let assump_80 := assump_60 assump_85
            apply False.elim assump_80


variable (p1 p4 p2 p3 p0 p6 p5 p7 : Prop)
theorem file49_107032 : (((((p2 → p6) → False) → ((p4 → p6) → False)) → (((p6 ∨ p7) ∨ (p7 ∨ False)) ∧ ((False ∧ True) ∨ (p7 ∨ p7)))) → ((((p7 ∨ False) ∧ (False ∧ False)) ∧ ((p1 → p5) ∨ (p4 → False))) → (((p1 → p3) ∨ (p7 ∨ p3)) → ((p6 ∨ p6) ∨ (p7 ∨ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
        case inr assump_13 =>
          apply False.elim assump_13
  case inr assump_5 =>
    cases assump_5
    case inl assump_22 =>
      cases assump_2
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_28
          case inl assump_30 =>
            cases assump_29
            case intro assump_34 assump_35 =>
              apply False.elim assump_34
          case inr assump_31 =>
            apply False.elim assump_31
    case inr assump_23 =>
      cases assump_2
      case intro assump_42 assump_43 =>
        cases assump_42
        case intro assump_44 assump_45 =>
          cases assump_44
          case inl assump_46 =>
            cases assump_45
            case intro assump_50 assump_51 =>
              apply False.elim assump_50
          case inr assump_47 =>
            apply False.elim assump_47


variable (p5 p6 p2 p7 p4 p1 : Prop)
theorem file49_108603 : (((((p6 ∧ p2) ∧ (False ∧ p4)) ∧ ((p6 ∧ False) → (p7 → p6))) ∧ (((p6 ∨ p5) ∧ (p2 ∧ False)) → ((p1 → False) ∧ (p7 → p5)))) → ((((p4 ∨ p2) ∨ (p4 → False)) → False) → False)) := by
  intro assump_28
  intro assump_29
  cases assump_28
  case intro assump_32 assump_33 =>
    cases assump_32
    case intro assump_34 assump_35 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          cases assump_37
          case intro assump_44 assump_45 =>
            apply False.elim assump_44


variable (p3 p5 p6 p1 p4 p7 p0 p2 : Prop)
theorem file49_109231 : (((((False → False) → (p0 → False)) → ((p7 ∨ p0) → (p5 → True))) ∨ (((p1 → False) ∨ (p0 → p2)) ∨ ((p6 → p1) ∧ (p1 → False)))) ∨ ((((p0 ∨ p4) → False) ∨ ((p5 → p3) ∨ (True ∧ p1))) ∨ (((p1 → False) ∧ (p2 → p4)) ∨ ((p5 → False) ∧ (p6 ∧ p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply True.intro


variable (p6 p2 p7 p4 : Prop)
theorem file49_109632 : (((((False → p2) ∨ (p2 → False)) → False) → False) ∨ ((((p6 ∨ p7) → False) ∧ ((True ∨ True) → False)) → (((p4 → False) → False) → ((p7 ∨ p7) ∨ (False → True))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → p2) ∨ (p2 → False)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p6 p2 p0 p5 p7 p3 : Prop)
theorem file49_110081 : (((((p0 → p2) → False) → ((True → False) → (p3 → p7))) → (((p2 → p2) ∨ (False → False)) ∨ ((p2 → p5) ∨ (p4 → False)))) ∧ ((((p6 → True) ∨ (p4 ∨ p5)) ∧ ((p5 → True) → False)) → False)) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  exact assump_4
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      have assump_41 : (p5 → True) := by
        intro assump_17
        apply True.intro
      let assump_16 := assump_9 assump_41
      apply False.elim assump_16
    case inr assump_11 =>
      cases assump_11
      case inl assump_21 =>
        have assump_42 : (p5 → True) := by
          intro assump_28
          apply True.intro
        let assump_27 := assump_9 assump_42
        apply False.elim assump_27
      case inr assump_22 =>
        have assump_43 : (p5 → True) := by
          intro assump_37
          apply True.intro
        let assump_36 := assump_9 assump_43
        apply False.elim assump_36


variable (p0 p6 p3 p7 p1 p2 p5 p4 : Prop)
theorem file49_111168 : (((((p5 ∨ p7) ∨ (p3 ∨ False)) ∨ ((p5 ∨ p5) ∧ (True → False))) ∨ (((p6 ∨ p6) → False) → ((p6 → False) ∨ (False → p0)))) ∨ ((((p0 ∧ p6) ∨ (p5 ∨ True)) → ((p1 → False) → (p2 ∨ False))) ∨ (((True ∨ p2) → (p6 ∨ p7)) ∧ ((p4 ∨ p4) → False)))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_12 : (p6 ∨ p6) := by
    apply Or.inl
    exact assump_4
  let assump_8 := assump_1 assump_12
  apply False.elim assump_8


variable (p6 p5 p1 p2 p0 : Prop)
theorem file49_111682 : ((((((False → p2) ∧ (p6 → False)) → ((False → p6) ∨ (p0 ∨ p1))) → (((False ∧ False) → (p1 ∧ p5)) ∨ ((p0 ∨ p2) ∧ (p2 → p2)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False → p2) ∧ (p6 → False)) → ((False → p6) ∨ (p0 ∨ p1))) → (((False ∧ False) → (p1 ∧ p5)) ∨ ((p0 ∨ p2) ∧ (p2 → p2)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply And.intro
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
    cases assump_8
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p4 p7 p6 p2 p0 p3 p5 p1 : Prop)
theorem file49_112380 : (((((p2 ∨ p3) ∨ (p5 → p2)) ∧ ((True → True) → False)) → (((p0 ∧ p6) ∨ (True ∧ False)) → ((False → False) ∨ (p3 ∧ p5)))) ∨ ((((p1 ∨ p6) → False) ∧ ((p0 ∧ p2) → False)) → (((p4 → False) → False) ∨ ((p0 ∧ p7) ∧ (p5 → p1))))) := by
  apply Or.inl
  intro assump_52
  intro assump_53
  cases assump_53
  case inl assump_54 =>
    cases assump_54
    case intro assump_56 assump_57 =>
      cases assump_52
      case intro assump_62 assump_63 =>
        cases assump_62
        case inl assump_64 =>
          cases assump_64
          case inl assump_66 =>
            apply Or.inl
            intro assump_72
            apply False.elim assump_72
          case inr assump_67 =>
            apply Or.inl
            intro assump_79
            apply False.elim assump_79
        case inr assump_65 =>
          apply Or.inl
          intro assump_86
          apply False.elim assump_86
  case inr assump_55 =>
    cases assump_55
    case intro assump_89 assump_90 =>
      apply False.elim assump_90


variable (p3 p1 p0 : Prop)
theorem file49_113431 : (((((False ∧ True) ∧ (p3 → p0)) ∨ ((False ∨ False) ∨ (False ∧ True))) ∧ (((True → False) → False) ∧ ((p3 → False) ∨ (False → p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8
    case inr assump_5 =>
      cases assump_5
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          apply False.elim assump_15
      case inr assump_13 =>
        cases assump_13
        case intro assump_20 assump_21 =>
          apply False.elim assump_20


variable (p0 p1 p6 : Prop)
theorem file49_114262 : ((((((True ∨ p0) ∨ (p1 ∧ True)) → False) → (((p6 → False) ∨ (p6 ∧ p1)) → False)) → False) → False) := by
  intro assump_1
  have assump_32 : ((((True ∨ p0) ∨ (p1 ∧ True)) → False) → (((p6 → False) ∨ (p6 ∧ p1)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_33 : ((True ∨ p0) ∨ (p1 ∧ True)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_13 := assump_5 assump_33
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case intro assump_17 assump_18 =>
        have assump_34 : ((True ∨ p0) ∨ (p1 ∧ True)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_25 := assump_5 assump_34
        apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


