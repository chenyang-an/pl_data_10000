variable (p3 p7 p2 p6 p5 : Prop)
theorem file29_41 : ((((((False ∧ p2) → (True → p3)) ∨ ((p6 ∨ p5) → (False ∧ p7))) ∨ (((False → False) → False) → ((p5 ∨ p5) → (p3 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False ∧ p2) → (True → p3)) ∨ ((p6 ∨ p5) → (False ∧ p7))) ∨ (((False → False) → False) → ((p5 ∨ p5) → (p3 ∧ False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p3 p6 p1 p4 : Prop)
theorem file29_633 : ((((((False ∧ p6) ∧ (p3 ∧ p3)) → False) ∨ (((p1 ∨ p4) ∧ (p7 → p1)) ∨ ((p1 ∨ True) ∧ (p6 → True)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∧ p6) ∧ (p3 ∧ p3)) → False) ∨ (((p1 ∨ p4) ∧ (p7 → p1)) ∨ ((p1 ∨ True) ∧ (p6 → True)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p7 p6 p4 : Prop)
theorem file29_1198 : ((((((False → False) → False) → False) ∨ (((p7 ∨ p7) ∨ (False → False)) ∨ ((p3 ∨ p6) ∨ (p4 → True)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((p7 ∨ p7) ∨ (False → False)) ∨ ((p3 ∨ p6) ∨ (p4 → True)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p1 p3 p5 p4 p0 : Prop)
theorem file29_1792 : (((((p4 ∨ p5) ∨ (False → False)) → False) → (((False → p5) → False) → False)) ∨ ((((p2 → p0) → False) → False) ∧ (((p3 ∨ p1) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_14 : ((p4 ∨ p5) ∨ (False → False)) := by
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p2 p5 p0 p4 p1 : Prop)
theorem file29_2235 : (((((True → False) → False) ∧ ((p1 ∧ True) ∧ (False → False))) ∨ (((p1 ∧ p0) ∧ (p0 ∧ False)) → False)) ∨ ((((False → False) ∨ (p4 ∧ p0)) → ((False ∧ False) ∧ (p2 → p5))) → False)) := by
  apply Or.inl
  apply Or.inr
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_14
      case intro assump_21 assump_22 =>
        apply False.elim assump_22


variable (p3 p7 p0 p1 p2 p6 p4 : Prop)
theorem file29_2741 : (((((p2 ∧ p1) ∨ (p3 ∧ p3)) → False) ∧ (((True → p4) → False) ∧ ((p2 ∧ p6) ∨ (p4 ∨ p0)))) → ((((p7 → p3) → False) ∨ ((p3 ∧ p6) → False)) → (((False → False) ∨ (p6 ∧ p2)) ∨ ((p2 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply Or.inl
            apply Or.inl
            intro assump_23
            apply False.elim assump_23
        case inr assump_16 =>
          cases assump_16
          case inl assump_26 =>
            apply Or.inl
            apply Or.inl
            intro assump_30
            apply False.elim assump_30
          case inr assump_27 =>
            apply Or.inl
            apply Or.inl
            intro assump_35
            apply False.elim assump_35
  case inr assump_4 =>
    cases assump_1
    case intro assump_40 assump_41 =>
      cases assump_41
      case intro assump_44 assump_45 =>
        cases assump_45
        case inl assump_48 =>
          cases assump_48
          case intro assump_50 assump_51 =>
            apply Or.inl
            apply Or.inl
            intro assump_56
            apply False.elim assump_56
        case inr assump_49 =>
          cases assump_49
          case inl assump_59 =>
            apply Or.inl
            apply Or.inl
            intro assump_63
            apply False.elim assump_63
          case inr assump_60 =>
            apply Or.inl
            apply Or.inl
            intro assump_68
            apply False.elim assump_68


variable (p0 p1 : Prop)
theorem file29_4514 : (((((False ∧ False) ∨ (p1 → True)) → False) ∧ (((False ∧ p0) → False) ∨ ((False → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_25 : ((False ∧ False) ∨ (p1 → True)) := by
        apply Or.inr
        intro assump_12
        apply True.intro
      let assump_11 := assump_2 assump_25
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_26 : (False → False) := by
        intro assump_19
        apply False.elim assump_19
      let assump_18 := assump_7 assump_26
      apply False.elim assump_18


variable (p7 p1 p0 p6 p3 p4 p5 p2 : Prop)
theorem file29_5217 : ((((((p7 ∧ p3) → False) → False) → False) ∧ ((((p0 → False) ∨ (p2 ∨ p2)) ∨ ((p5 ∨ p4) → False)) ∧ (((p1 → p2) → False) ∧ ((p5 → p5) → (p2 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            have assump_116 : (p1 → p2) := by
              intro assump_28
              have assump_117 : (p5 → p5) := by
                intro assump_33
                exact assump_33
              let assump_32 := assump_15 assump_117
              let assump_36 := And.left assump_32
              exact assump_36
            let assump_27 := assump_14 assump_116
            apply False.elim assump_27
        case inr assump_11 =>
          cases assump_11
          case inl assump_41 =>
            cases assump_7
            case intro assump_45 assump_46 =>
              have assump_118 : (p1 → p2) := by
                intro assump_59
                exact assump_41
              let assump_58 := assump_45 assump_118
              apply False.elim assump_58
          case inr assump_42 =>
            cases assump_7
            case intro assump_67 assump_68 =>
              have assump_119 : (p1 → p2) := by
                intro assump_81
                exact assump_42
              let assump_80 := assump_67 assump_119
              apply False.elim assump_80
      case inr assump_9 =>
        cases assump_7
        case intro assump_89 assump_90 =>
          have assump_120 : (p1 → p2) := by
            intro assump_103
            have assump_121 : (p5 → p5) := by
              intro assump_108
              exact assump_108
            let assump_107 := assump_90 assump_121
            let assump_111 := And.left assump_107
            exact assump_111
          let assump_102 := assump_89 assump_120
          apply False.elim assump_102


variable (p3 p7 p1 p4 : Prop)
theorem file29_7302 : ((((((p4 ∨ p4) ∧ (True ∧ p3)) ∨ ((p1 → False) → (p4 → True))) ∨ (((p7 ∧ False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_10 : ((((p4 ∨ p4) ∧ (True ∧ p3)) ∨ ((p1 → False) → (p4 → True))) ∨ (((p7 ∧ False) → False) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p6 p2 p3 : Prop)
theorem file29_7771 : (((((True → False) → (p6 → False)) → False) → False) ∨ ((((p3 ∧ p3) → (p2 ∨ p2)) → ((True → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((True → False) → (p6 → False)) := by
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p3 p7 p5 p0 p6 p1 : Prop)
theorem file29_8277 : ((((((True → p7) ∧ (False ∧ p7)) ∧ ((p6 → True) ∧ (p5 ∧ p5))) ∧ (((p1 ∨ p2) ∨ (p2 → p0)) → ((p7 → False) → False))) ∧ ((((p3 ∨ p6) ∨ (p7 ∨ p5)) → ((False → False) ∧ (p3 ∨ p1))) ∧ (((p2 → p5) ∨ (p5 → p1)) → False))) → False) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          cases assump_28
          case intro assump_31 assump_32 =>
            apply False.elim assump_31


variable (p6 p5 p4 p3 p7 : Prop)
theorem file29_8931 : ((((((False ∧ p4) ∧ (p5 ∨ True)) ∧ ((p7 ∨ p6) ∨ (p3 ∨ p4))) → False) → False) → False) := by
  intro assump_1
  have assump_17 : ((((False ∧ p4) ∧ (p5 ∨ True)) ∧ ((p7 ∨ p6) ∨ (p3 ∨ p4))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p3 p5 p0 p1 : Prop)
theorem file29_9487 : ((((((p5 ∧ p0) ∧ (False ∨ p5)) ∧ ((p5 ∨ p0) ∧ (False ∧ False))) → (((p3 → False) ∧ (p3 ∨ p1)) → False)) → False) → False) := by
  intro assump_11
  have assump_94 : ((((p5 ∧ p0) ∧ (False ∨ p5)) ∧ ((p5 ∨ p0) ∧ (False ∧ False))) → (((p3 → False) ∧ (p3 ∨ p1)) → False)) := by
    intro assump_15
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      cases assump_18
      case inl assump_21 =>
        cases assump_15
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            cases assump_27
            case intro assump_29 assump_30 =>
              cases assump_28
              case inl assump_35 =>
                apply False.elim assump_35
              case inr assump_36 =>
                cases assump_26
                case intro assump_41 assump_42 =>
                  cases assump_41
                  case inl assump_43 =>
                    cases assump_42
                    case intro assump_47 assump_48 =>
                      apply False.elim assump_47
                  case inr assump_44 =>
                    cases assump_42
                    case intro assump_53 assump_54 =>
                      apply False.elim assump_53
      case inr assump_22 =>
        cases assump_15
        case intro assump_59 assump_60 =>
          cases assump_59
          case intro assump_61 assump_62 =>
            cases assump_61
            case intro assump_63 assump_64 =>
              cases assump_62
              case inl assump_69 =>
                apply False.elim assump_69
              case inr assump_70 =>
                cases assump_60
                case intro assump_75 assump_76 =>
                  cases assump_75
                  case inl assump_77 =>
                    cases assump_76
                    case intro assump_81 assump_82 =>
                      apply False.elim assump_81
                  case inr assump_78 =>
                    cases assump_76
                    case intro assump_87 assump_88 =>
                      apply False.elim assump_87
  let assump_14 := assump_11 assump_94
  apply False.elim assump_14


variable (p4 p1 p5 p2 p7 p6 : Prop)
theorem file29_11722 : (((((True ∧ p7) ∧ (p7 → False)) ∧ ((p5 ∨ p1) ∨ (p7 → p2))) → False) ∧ ((((True ∧ p6) → False) ∨ ((True ∧ p4) ∨ (True → False))) → (((p2 ∨ p4) → (True ∧ p1)) → ((True ∨ p4) → (p6 → p4))))) := by
  apply And.intro
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_11
        case inl assump_22 =>
          cases assump_22
          case inl assump_24 =>
            have assump_100 : p7 := by
              exact assump_15
            let assump_29 := assump_13 assump_100
            apply False.elim assump_29
          case inr assump_25 =>
            have assump_101 : p7 := by
              exact assump_15
            let assump_36 := assump_13 assump_101
            apply False.elim assump_36
        case inr assump_23 =>
          have assump_102 : p7 := by
            exact assump_15
          let assump_44 := assump_13 assump_102
          apply False.elim assump_44
  intro assump_48
  intro assump_49
  intro assump_50
  intro assump_51
  cases assump_50
  case inl assump_54 =>
    cases assump_48
    case inl assump_60 =>
      have assump_103 : (True ∧ p6) := by
        apply And.intro
        apply True.intro
        exact assump_51
      let assump_64 := assump_60 assump_103
      apply False.elim assump_64
    case inr assump_61 =>
      cases assump_61
      case inl assump_68 =>
        cases assump_68
        case intro assump_70 assump_71 =>
          exact assump_71
      case inr assump_69 =>
        have assump_104 : True := by
          apply True.intro
        let assump_78 := assump_69 assump_104
        apply False.elim assump_78
  case inr assump_55 =>
    cases assump_48
    case inl assump_86 =>
      exact assump_55
    case inr assump_87 =>
      cases assump_87
      case inl assump_90 =>
        cases assump_90
        case intro assump_92 assump_93 =>
          exact assump_93
      case inr assump_91 =>
        exact assump_55


theorem file29_13793 : (((((False → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → False) → False) → False) := by
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p5 p7 p3 p4 p6 p2 p1 : Prop)
theorem file29_14248 : ((((((p3 → p4) → False) → False) ∨ (((p0 ∨ p3) ∧ (p5 ∧ True)) ∧ ((p7 → p3) → (p3 ∨ p1)))) ∧ ((((p6 ∨ True) ∧ (False → False)) ∨ ((p2 ∨ p6) → (p3 ∨ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_61 : (((p6 ∨ True) ∧ (False → False)) ∨ ((p2 ∨ p6) → (p3 ∨ p5))) := by
        apply Or.inl
        apply And.intro
        apply Or.inr
        apply True.intro
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_3 assump_61
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_19
          case inl assump_21 =>
            cases assump_20
            case intro assump_25 assump_26 =>
              have assump_62 : (((p6 ∨ True) ∧ (False → False)) ∨ ((p2 ∨ p6) → (p3 ∨ p5))) := by
                apply Or.inl
                apply And.intro
                apply Or.inr
                apply True.intro
                intro assump_36
                apply False.elim assump_36
              let assump_35 := assump_3 assump_62
              apply False.elim assump_35
          case inr assump_22 =>
            cases assump_20
            case intro assump_44 assump_45 =>
              have assump_63 : (((p6 ∨ True) ∧ (False → False)) ∨ ((p2 ∨ p6) → (p3 ∨ p5))) := by
                apply Or.inl
                apply And.intro
                apply Or.inr
                apply True.intro
                intro assump_55
                apply False.elim assump_55
              let assump_54 := assump_3 assump_63
              apply False.elim assump_54


variable (p0 p7 p6 p5 p2 p4 p1 : Prop)
theorem file29_16077 : (((((False → False) ∧ (p0 → True)) → False) ∨ (((True → False) → (p6 → p7)) → False)) → ((((p5 ∧ p5) ∨ (p6 ∨ p7)) → ((p2 ∨ p7) ∨ (p7 → False))) → (((p5 → False) ∨ (False ∧ p4)) → ((p4 → False) → (False → p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p4 p5 p0 p2 p3 p7 : Prop)
theorem file29_16468 : ((((((p2 ∨ p7) ∧ (p0 ∧ p4)) ∧ ((False ∧ p7) ∨ (p0 → p3))) ∨ (((True ∧ True) → False) ∧ ((p7 → False) → (p5 → False)))) ∧ ((((p0 ∨ True) ∨ (p0 → False)) ∨ ((p7 → False) ∧ (p4 → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_9
            case intro assump_14 assump_15 =>
              cases assump_7
              case inl assump_20 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  apply False.elim assump_22
              case inr assump_21 =>
                have assump_68 : (((p0 ∨ True) ∨ (p0 → False)) ∨ ((p7 → False) ∧ (p4 → p3))) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_14
                let assump_30 := assump_3 assump_68
                apply False.elim assump_30
          case inr assump_11 =>
            cases assump_9
            case intro assump_36 assump_37 =>
              cases assump_7
              case inl assump_42 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  apply False.elim assump_44
              case inr assump_43 =>
                have assump_69 : (((p0 ∨ True) ∨ (p0 → False)) ∨ ((p7 → False) ∧ (p4 → p3))) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_36
                let assump_52 := assump_3 assump_69
                apply False.elim assump_52
    case inr assump_5 =>
      cases assump_5
      case intro assump_56 assump_57 =>
        have assump_70 : (((p0 ∨ True) ∨ (p0 → False)) ∨ ((p7 → False) ∧ (p4 → p3))) := by
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_64 := assump_3 assump_70
        apply False.elim assump_64


variable (p3 p2 p4 p6 p0 p1 p5 : Prop)
theorem file29_18657 : (((((False ∧ p6) ∧ (p1 ∧ p6)) ∧ ((p5 ∧ p5) → (True ∧ p3))) → False) ∨ ((((p5 ∨ False) ∧ (p2 → False)) ∨ ((p4 → True) ∧ (p1 → p3))) ∨ (((p5 → False) ∨ (p0 → p3)) → ((p6 ∨ p4) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6


variable (p0 p6 p3 p4 p7 p1 p2 : Prop)
theorem file29_19143 : (((((p6 → p4) ∧ (p7 → False)) → False) → (((False ∧ p4) → False) → ((False → p6) ∨ (p4 → False)))) ∨ ((((p1 ∨ p6) → False) → ((False ∧ p1) ∨ (p0 → True))) → (((p0 ∨ True) → (p2 → p3)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p4 p6 p3 p1 : Prop)
theorem file29_19507 : (((((p6 → False) → False) ∧ ((p1 → False) ∨ (p4 ∨ p6))) → False) → ((((p6 → False) ∧ (True → False)) → ((p6 ∧ p3) → False)) ∨ (((True ∨ True) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case intro assump_12 assump_13 =>
      have assump_22 : True := by
        apply True.intro
      let assump_18 := assump_13 assump_22
      apply False.elim assump_18


variable (p2 p4 p5 p3 p7 p0 p1 : Prop)
theorem file29_20047 : (((((p1 → True) → False) → ((False ∧ p5) ∧ (p4 → p3))) ∧ (((True ∧ False) → (p2 ∨ p3)) → False)) → ((((p3 ∧ p3) ∧ (p5 ∧ p4)) → ((p7 → False) → (p0 → False))) → False)) := by
  intro assump_9
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    have assump_30 : ((True ∧ False) → (p2 ∨ p3)) := by
      intro assump_20
      cases assump_20
      case intro assump_21 assump_22 =>
        apply False.elim assump_22
    let assump_19 := assump_14 assump_30
    apply False.elim assump_19


variable (p0 p6 p7 p4 p1 p3 p5 : Prop)
theorem file29_20619 : ((((((p0 → False) → (p1 → p0)) → False) ∧ (((p5 ∨ p6) → False) ∨ ((p7 → p5) ∧ (p1 ∧ p7)))) ∧ ((((p3 ∨ p7) ∨ (p7 → False)) ∨ ((p3 → False) → (p4 ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_42 : (((p3 ∨ p7) ∨ (p7 → False)) ∨ ((p3 → False) → (p4 ∨ True))) := by
          apply Or.inl
          apply Or.inr
          intro assump_15
          have assump_43 : (((p3 ∨ p7) ∨ (p7 → False)) ∨ ((p3 → False) → (p4 ∨ True))) := by
            apply Or.inl
            apply Or.inl
            apply Or.inr
            exact assump_15
          let assump_19 := assump_3 assump_43
          apply False.elim assump_19
        let assump_14 := assump_3 assump_42
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case intro assump_26 assump_27 =>
          cases assump_27
          case intro assump_30 assump_31 =>
            have assump_44 : (((p3 ∨ p7) ∨ (p7 → False)) ∨ ((p3 → False) → (p4 ∨ True))) := by
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_31
            let assump_38 := assump_3 assump_44
            apply False.elim assump_38


variable (p1 p7 p4 p5 p0 p2 : Prop)
theorem file29_22005 : ((((((True ∨ p4) ∨ (p2 → p0)) → ((p4 ∧ p0) ∨ (p1 → p1))) ∨ (((p5 ∨ p4) ∨ (p7 → p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_28 : ((((True ∨ p4) ∨ (p2 → p0)) → ((p4 ∧ p0) ∨ (p1 → p1))) ∨ (((p5 ∨ p4) ∨ (p7 → p7)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inr
        intro assump_12
        exact assump_12
      case inr assump_9 =>
        apply Or.inr
        intro assump_17
        exact assump_17
    case inr assump_7 =>
      apply Or.inr
      intro assump_22
      exact assump_22
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p0 p1 p4 p7 p2 p3 : Prop)
theorem file29_22763 : (((((p4 → p4) → False) → ((p0 → False) ∧ (p7 ∧ p1))) → False) → ((((p3 → False) → (p2 ∧ p2)) ∧ ((p7 ∨ p3) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_46 : (((p4 → p4) → False) → ((p0 → False) ∧ (p7 ∧ p1))) := by
      intro assump_12
      apply And.intro
      intro assump_13
      have assump_47 : (p4 → p4) := by
        intro assump_19
        exact assump_19
      let assump_18 := assump_12 assump_47
      apply False.elim assump_18
      apply And.intro
      have assump_48 : (p4 → p4) := by
        intro assump_28
        exact assump_28
      let assump_27 := assump_12 assump_48
      apply False.elim assump_27
      have assump_49 : (p4 → p4) := by
        intro assump_37
        exact assump_37
      let assump_36 := assump_12 assump_49
      apply False.elim assump_36
    let assump_11 := assump_1 assump_46
    apply False.elim assump_11


variable (p1 p5 p0 p2 : Prop)
theorem file29_23760 : ((((((False ∨ p1) ∨ (p5 ∧ True)) → False) → False) ∧ ((((p2 → p2) → (False ∧ p0)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p2 → p2) → (False ∧ p0)) → False) := by
      intro assump_9
      have assump_24 : (p2 → p2) := by
        intro assump_13
        exact assump_13
      let assump_12 := assump_9 assump_24
      let assump_16 := And.left assump_12
      apply False.elim assump_16
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p7 p1 p0 p4 p5 p2 p6 : Prop)
theorem file29_24365 : (((((False → False) → (p4 → p0)) ∧ ((False → False) → False)) → False) ∨ ((((p6 → False) → False) ∨ ((p7 → p2) ∨ (p6 ∨ p6))) ∧ (((p1 ∧ p1) → False) → ((p5 ∧ True) ∧ (p6 ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p5 p4 p0 p7 p6 : Prop)
theorem file29_24858 : ((((((p4 ∧ p0) ∧ (p5 → False)) → False) ∧ (((p6 → p7) ∧ (p6 ∧ True)) ∧ ((True ∨ True) → (p4 → False)))) ∧ ((((p3 ∧ True) → (False ∧ p4)) → ((p6 → False) → (p4 ∧ True))) ∧ (((True ∨ p6) → (False → p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_3
            case intro assump_22 assump_23 =>
              have assump_36 : ((True ∨ p6) → (False → p5)) := by
                intro assump_29
                intro assump_30
                apply False.elim assump_30
              let assump_28 := assump_23 assump_36
              apply False.elim assump_28


variable (p3 p0 p7 p5 p1 p4 p2 p6 : Prop)
theorem file29_25806 : ((((((p2 → p0) → False) ∧ ((p7 → p5) ∧ (p0 → p6))) → (((True → p7) → False) ∧ ((p1 ∨ p5) → (p6 → p1)))) ∧ ((((p3 → False) ∨ (p3 → p4)) ∧ ((p6 → True) → (True → False))) ∧ (((p5 → False) ∧ (p0 ∧ p0)) ∧ ((p0 → False) ∨ (False → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_17
                case inl assump_28 =>
                  have assump_84 : p0 := by
                    exact assump_23
                  let assump_32 := assump_28 assump_84
                  apply False.elim assump_32
                case inr assump_29 =>
                  have assump_85 : (p6 → True) := by
                    intro assump_43
                    apply True.intro
                  let assump_42 := assump_9 assump_85
                  have assump_86 : True := by
                    apply True.intro
                  let assump_44 := assump_42 assump_86
                  apply False.elim assump_44
        case inr assump_11 =>
          cases assump_7
          case intro assump_52 assump_53 =>
            cases assump_52
            case intro assump_54 assump_55 =>
              cases assump_55
              case intro assump_58 assump_59 =>
                cases assump_53
                case inl assump_64 =>
                  have assump_87 : p0 := by
                    exact assump_59
                  let assump_68 := assump_64 assump_87
                  apply False.elim assump_68
                case inr assump_65 =>
                  have assump_88 : (p6 → True) := by
                    intro assump_79
                    apply True.intro
                  let assump_78 := assump_9 assump_88
                  have assump_89 : True := by
                    apply True.intro
                  let assump_80 := assump_78 assump_89
                  apply False.elim assump_80


variable (p2 p1 : Prop)
theorem file29_28115 : ((((((p1 → False) → False) → False) → (((p1 ∧ False) → (p1 ∨ p1)) ∨ ((p2 ∨ True) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 → False) → False) → False) → (((p1 ∧ False) → (p1 ∨ p1)) ∨ ((p2 ∨ True) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p2 p7 p0 p1 p5 p4 : Prop)
theorem file29_28635 : (((((p2 ∧ p7) → (p1 → True)) → False) ∧ (((p2 → p1) ∧ (p4 ∧ p3)) ∨ ((p1 ∨ p0) → (p5 ∨ p3)))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_9
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          have assump_42 : ((p2 ∧ p7) → (p1 → True)) := by
            intro assump_28
            intro assump_29
            apply True.intro
          let assump_27 := assump_8 assump_42
          apply False.elim assump_27
    case inr assump_13 =>
      have assump_43 : ((p2 ∧ p7) → (p1 → True)) := by
        intro assump_37
        intro assump_38
        apply True.intro
      let assump_36 := assump_8 assump_43
      apply False.elim assump_36


variable (p5 p6 p3 p7 p1 p2 p0 : Prop)
theorem file29_29503 : (((((p6 ∨ p7) → (p6 → False)) → False) → (((p5 → False) → (p3 ∨ p1)) → ((False ∨ True) ∨ (True → False)))) ∨ ((((p2 → False) ∨ (p0 → False)) ∧ ((True → p1) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p7 p6 p5 p4 p3 p0 : Prop)
theorem file29_29843 : ((((((True ∨ False) → False) ∧ ((p4 ∨ p3) ∧ (p6 → False))) → (((p5 ∧ p0) ∧ (p3 ∧ p7)) ∧ ((p5 → True) → False))) → False) → False) := by
  intro assump_1
  have assump_146 : ((((True ∨ False) → False) ∧ ((p4 ∨ p3) ∧ (p6 → False))) → (((p5 ∧ p0) ∧ (p3 ∧ p7)) ∧ ((p5 → True) → False))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_147 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_20 := assump_6 assump_147
          apply False.elim assump_20
        case inr assump_13 =>
          have assump_148 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_30 := assump_6 assump_148
          apply False.elim assump_30
    cases assump_5
    case intro assump_34 assump_35 =>
      cases assump_35
      case intro assump_38 assump_39 =>
        cases assump_38
        case inl assump_40 =>
          have assump_149 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_48 := assump_34 assump_149
          apply False.elim assump_48
        case inr assump_41 =>
          have assump_150 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_58 := assump_34 assump_150
          apply False.elim assump_58
    apply And.intro
    cases assump_5
    case intro assump_62 assump_63 =>
      cases assump_63
      case intro assump_66 assump_67 =>
        cases assump_66
        case inl assump_68 =>
          have assump_151 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_76 := assump_62 assump_151
          apply False.elim assump_76
        case inr assump_69 =>
          exact assump_69
    cases assump_5
    case intro assump_84 assump_85 =>
      cases assump_85
      case intro assump_88 assump_89 =>
        cases assump_88
        case inl assump_90 =>
          have assump_152 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_98 := assump_84 assump_152
          apply False.elim assump_98
        case inr assump_91 =>
          have assump_153 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_108 := assump_84 assump_153
          apply False.elim assump_108
    intro assump_112
    cases assump_5
    case intro assump_115 assump_116 =>
      cases assump_116
      case intro assump_119 assump_120 =>
        cases assump_119
        case inl assump_121 =>
          have assump_154 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_129 := assump_115 assump_154
          apply False.elim assump_129
        case inr assump_122 =>
          have assump_155 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_139 := assump_115 assump_155
          apply False.elim assump_139
  let assump_4 := assump_1 assump_146
  apply False.elim assump_4


variable (p6 p4 p3 p7 p5 p2 p0 : Prop)
theorem file29_33125 : (((((p2 → p4) → (True ∨ p6)) ∨ ((p2 → p6) → (p0 ∧ p0))) ∨ (((True → False) ∧ (p5 ∧ p0)) ∧ ((True ∧ p5) ∧ (p2 ∨ True)))) ∨ ((((p5 ∨ p4) → (p3 → False)) ∧ ((p6 → False) ∨ (p3 → False))) ∨ (((p7 → False) ∨ (p2 ∧ p0)) ∨ ((p4 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply True.intro


variable (p7 p1 : Prop)
theorem file29_33517 : ((((((p1 ∨ p1) → False) ∧ ((p7 ∨ True) → False)) → False) → False) → False) := by
  intro assump_12
  have assump_30 : ((((p1 ∨ p1) → False) ∧ ((p7 ∨ True) → False)) → False) := by
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      have assump_31 : (p7 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_23 := assump_18 assump_31
      apply False.elim assump_23
  let assump_15 := assump_12 assump_30
  apply False.elim assump_15


variable (p1 p6 p0 p7 p2 p5 p4 p3 : Prop)
theorem file29_34073 : (((((True → False) ∧ (p2 ∧ p1)) → False) ∨ (((p6 → True) ∨ (False ∨ p1)) → ((p5 → False) → (p7 → False)))) ∨ ((((True ∨ p0) → False) ∧ ((p6 → False) → (p5 ∧ True))) → (((p3 → False) → (p1 ∧ p2)) ∨ ((p4 → False) → (p4 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_18 : True := by
        apply True.intro
      let assump_14 := assump_2 assump_18
      apply False.elim assump_14


variable (p0 p4 p5 p3 p2 p1 p7 : Prop)
theorem file29_34656 : (((((p0 ∧ p7) → (p5 ∨ p7)) ∧ ((p5 ∧ p2) → (p2 ∨ True))) → False) → ((((p0 ∨ p2) ∨ (False → p1)) ∧ ((p5 → True) → False)) → (((p4 → p3) → False) ∧ ((p0 ∧ True) ∧ (p7 → p1))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        have assump_225 : (((p0 ∧ p7) → (p5 ∨ p7)) ∧ ((p5 ∧ p2) → (p2 ∨ True))) := by
          apply And.intro
          intro assump_19
          cases assump_19
          case intro assump_20 assump_21 =>
            apply Or.inr
            exact assump_21
          intro assump_26
          cases assump_26
          case intro assump_27 assump_28 =>
            apply Or.inl
            exact assump_28
        let assump_18 := assump_1 assump_225
        apply False.elim assump_18
      case inr assump_11 =>
        have assump_226 : (((p0 ∧ p7) → (p5 ∨ p7)) ∧ ((p5 ∧ p2) → (p2 ∨ True))) := by
          apply And.intro
          intro assump_43
          cases assump_43
          case intro assump_44 assump_45 =>
            apply Or.inr
            exact assump_45
          intro assump_50
          cases assump_50
          case intro assump_51 assump_52 =>
            apply Or.inl
            exact assump_52
        let assump_42 := assump_1 assump_226
        apply False.elim assump_42
    case inr assump_9 =>
      have assump_227 : (((p0 ∧ p7) → (p5 ∨ p7)) ∧ ((p5 ∧ p2) → (p2 ∨ True))) := by
        apply And.intro
        intro assump_67
        cases assump_67
        case intro assump_68 assump_69 =>
          apply Or.inr
          exact assump_69
        intro assump_74
        cases assump_74
        case intro assump_75 assump_76 =>
          apply Or.inl
          exact assump_76
      let assump_66 := assump_1 assump_227
      apply False.elim assump_66
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_84 assump_85 =>
    cases assump_84
    case inl assump_86 =>
      cases assump_86
      case inl assump_88 =>
        exact assump_88
      case inr assump_89 =>
        have assump_228 : (((p0 ∧ p7) → (p5 ∨ p7)) ∧ ((p5 ∧ p2) → (p2 ∨ True))) := by
          apply And.intro
          intro assump_103
          cases assump_103
          case intro assump_104 assump_105 =>
            apply Or.inr
            exact assump_105
          intro assump_110
          cases assump_110
          case intro assump_111 assump_112 =>
            apply Or.inl
            exact assump_112
        let assump_102 := assump_1 assump_228
        apply False.elim assump_102
    case inr assump_87 =>
      have assump_229 : (((p0 ∧ p7) → (p5 ∨ p7)) ∧ ((p5 ∧ p2) → (p2 ∨ True))) := by
        apply And.intro
        intro assump_127
        cases assump_127
        case intro assump_128 assump_129 =>
          apply Or.inr
          exact assump_129
        intro assump_134
        cases assump_134
        case intro assump_135 assump_136 =>
          apply Or.inl
          exact assump_136
      let assump_126 := assump_1 assump_229
      apply False.elim assump_126
  apply True.intro
  intro assump_144
  cases assump_2
  case intro assump_147 assump_148 =>
    cases assump_147
    case inl assump_149 =>
      cases assump_149
      case inl assump_151 =>
        have assump_230 : (((p0 ∧ p7) → (p5 ∨ p7)) ∧ ((p5 ∧ p2) → (p2 ∨ True))) := by
          apply And.intro
          intro assump_160
          cases assump_160
          case intro assump_161 assump_162 =>
            apply Or.inr
            exact assump_162
          intro assump_167
          cases assump_167
          case intro assump_168 assump_169 =>
            apply Or.inl
            exact assump_169
        let assump_159 := assump_1 assump_230
        apply False.elim assump_159
      case inr assump_152 =>
        have assump_231 : (((p0 ∧ p7) → (p5 ∨ p7)) ∧ ((p5 ∧ p2) → (p2 ∨ True))) := by
          apply And.intro
          intro assump_184
          cases assump_184
          case intro assump_185 assump_186 =>
            apply Or.inr
            exact assump_186
          intro assump_191
          cases assump_191
          case intro assump_192 assump_193 =>
            apply Or.inl
            exact assump_193
        let assump_183 := assump_1 assump_231
        apply False.elim assump_183
    case inr assump_150 =>
      have assump_232 : (((p0 ∧ p7) → (p5 ∨ p7)) ∧ ((p5 ∧ p2) → (p2 ∨ True))) := by
        apply And.intro
        intro assump_208
        cases assump_208
        case intro assump_209 assump_210 =>
          apply Or.inr
          exact assump_210
        intro assump_215
        cases assump_215
        case intro assump_216 assump_217 =>
          apply Or.inl
          exact assump_217
      let assump_207 := assump_1 assump_232
      apply False.elim assump_207


variable (p4 p3 p5 p2 p6 p7 p1 p0 : Prop)
theorem file29_39577 : (((((False ∧ p7) ∧ (p2 ∨ p0)) ∧ ((False → p2) → (p0 ∧ p6))) → (((p5 → False) ∨ (p5 ∨ p0)) → ((p4 ∨ p1) → (True ∨ p0)))) ∨ ((((p1 → p3) → (p3 ∨ p0)) ∨ ((False ∧ p5) → (p5 ∨ p0))) → (((p7 → p4) → (p6 ∨ p4)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_1
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
    case inr assump_9 =>
      cases assump_9
      case inl assump_20 =>
        cases assump_1
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            cases assump_26
            case intro assump_28 assump_29 =>
              apply False.elim assump_28
      case inr assump_21 =>
        cases assump_1
        case intro assump_34 assump_35 =>
          cases assump_34
          case intro assump_36 assump_37 =>
            cases assump_36
            case intro assump_38 assump_39 =>
              apply False.elim assump_38
  case inr assump_5 =>
    cases assump_2
    case inl assump_44 =>
      cases assump_1
      case intro assump_48 assump_49 =>
        cases assump_48
        case intro assump_50 assump_51 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            apply False.elim assump_52
    case inr assump_45 =>
      cases assump_45
      case inl assump_56 =>
        cases assump_1
        case intro assump_60 assump_61 =>
          cases assump_60
          case intro assump_62 assump_63 =>
            cases assump_62
            case intro assump_64 assump_65 =>
              apply False.elim assump_64
      case inr assump_57 =>
        cases assump_1
        case intro assump_70 assump_71 =>
          cases assump_70
          case intro assump_72 assump_73 =>
            cases assump_72
            case intro assump_74 assump_75 =>
              apply False.elim assump_74


variable (p2 p5 p0 p3 p4 p6 : Prop)
theorem file29_41755 : (((((True ∧ p0) ∧ (p0 → False)) → False) ∨ (((p0 → p2) → False) → False)) ∨ ((((p3 → p5) → False) ∧ ((p5 ∨ p6) ∨ (p4 ∨ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : p0 := by
        exact assump_5
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p4 p6 p2 p3 : Prop)
theorem file29_42233 : ((((((p2 ∨ True) → False) → ((p6 → p2) → False)) → False) ∧ ((((p3 ∨ False) ∧ (p4 ∧ p2)) → False) ∨ (((True → False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_38 : (((p2 ∨ True) → False) → ((p6 → p2) → False)) := by
        intro assump_12
        intro assump_13
        have assump_39 : (p2 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_18 := assump_12 assump_39
        apply False.elim assump_18
      let assump_11 := assump_2 assump_38
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_40 : ((True → False) → False) := by
        intro assump_28
        have assump_41 : True := by
          apply True.intro
        let assump_31 := assump_28 assump_41
        apply False.elim assump_31
      let assump_27 := assump_7 assump_40
      apply False.elim assump_27


variable (p0 p2 p7 p1 p5 p6 p3 p4 : Prop)
theorem file29_43255 : (((((p3 ∨ True) → False) ∨ ((p6 ∨ p6) ∨ (p1 ∨ p7))) ∧ (((p6 ∨ p3) → False) → ((p2 ∧ p2) → False))) → ((((p5 → False) ∧ (p0 ∧ False)) ∧ ((p4 ∨ p3) → (p2 → False))) → (((p5 → p3) ∨ (p6 ∨ p7)) → ((p0 ∧ False) → (p3 → p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_9


variable (p1 p7 p5 p3 p0 : Prop)
theorem file29_43706 : ((((((p0 ∧ p3) ∧ (False ∨ p0)) ∧ ((p1 ∧ p0) ∨ (p3 → p7))) → (((False → p7) → False) → ((p5 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_65 : ((((p0 ∧ p3) ∧ (False ∨ p0)) ∧ ((p1 ∧ p0) ∨ (p3 → p7))) → (((False → p7) → False) → ((p5 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_15
          case inl assump_22 =>
            apply False.elim assump_22
          case inr assump_23 =>
            cases assump_13
            case inl assump_28 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                have assump_66 : (False → p7) := by
                  intro assump_42
                  apply False.elim assump_42
                let assump_41 := assump_6 assump_66
                apply False.elim assump_41
            case inr assump_29 =>
              have assump_67 : (False → p7) := by
                intro assump_56
                apply False.elim assump_56
              let assump_55 := assump_6 assump_67
              apply False.elim assump_55
  let assump_4 := assump_1 assump_65
  apply False.elim assump_4


variable (p0 p1 p3 p6 p2 : Prop)
theorem file29_45101 : ((((((p3 ∨ p1) → False) ∧ ((p0 ∨ p6) → False)) ∨ (((p0 → False) ∧ (p2 → p2)) ∨ ((p1 ∧ p0) ∧ (p2 → False)))) ∧ ((((p1 → p6) → False) ∧ ((False → p0) ∧ (p2 ∧ False))) ∧ (((True → p0) → False) → ((False → p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                apply False.elim assump_23
    case inr assump_5 =>
      cases assump_5
      case inl assump_28 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_3
          case intro assump_36 assump_37 =>
            cases assump_36
            case intro assump_38 assump_39 =>
              cases assump_39
              case intro assump_42 assump_43 =>
                cases assump_43
                case intro assump_46 assump_47 =>
                  apply False.elim assump_47
      case inr assump_29 =>
        cases assump_29
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_3
            case intro assump_62 assump_63 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                cases assump_65
                case intro assump_68 assump_69 =>
                  cases assump_69
                  case intro assump_72 assump_73 =>
                    apply False.elim assump_73


variable (p5 p1 p4 p0 p6 p3 p7 p2 : Prop)
theorem file29_46919 : (((((p4 → p1) → False) ∨ ((p2 ∨ p1) ∨ (p4 → p3))) ∧ (((p7 → False) → False) ∧ ((p7 ∨ p1) ∨ (False ∧ p1)))) → ((((p1 → False) ∧ (p5 ∨ p3)) ∧ ((p2 ∧ False) ∧ (True → p1))) → (((p0 ∧ p6) → False) ∧ ((p0 → False) → False)))) := by
  intro assump_12
  intro assump_13
  apply And.intro
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_13
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_24
        case inl assump_27 =>
          cases assump_22
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              apply False.elim assump_34
        case inr assump_28 =>
          cases assump_22
          case intro assump_41 assump_42 =>
            cases assump_41
            case intro assump_43 assump_44 =>
              apply False.elim assump_44
  intro assump_49
  cases assump_13
  case intro assump_52 assump_53 =>
    cases assump_52
    case intro assump_54 assump_55 =>
      cases assump_55
      case inl assump_58 =>
        cases assump_53
        case intro assump_62 assump_63 =>
          cases assump_62
          case intro assump_64 assump_65 =>
            apply False.elim assump_65
      case inr assump_59 =>
        cases assump_53
        case intro assump_72 assump_73 =>
          cases assump_72
          case intro assump_74 assump_75 =>
            apply False.elim assump_75


variable (p2 p5 p4 p6 p0 p1 : Prop)
theorem file29_48464 : (((((p5 ∨ p2) ∧ (p6 ∨ False)) ∧ ((True → False) ∧ (p4 ∧ p0))) → False) ∨ ((((p1 ∨ p5) ∨ (p0 ∨ False)) ∨ ((True → False) ∧ (p0 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              have assump_56 : True := by
                apply True.intro
              let assump_26 := assump_14 assump_56
              apply False.elim assump_26
        case inr assump_11 =>
          apply False.elim assump_11
      case inr assump_7 =>
        cases assump_5
        case inl assump_34 =>
          cases assump_3
          case intro assump_38 assump_39 =>
            cases assump_39
            case intro assump_42 assump_43 =>
              have assump_57 : True := by
                apply True.intro
              let assump_50 := assump_38 assump_57
              apply False.elim assump_50
        case inr assump_35 =>
          apply False.elim assump_35


variable (p2 p6 p0 p5 p1 p3 p4 : Prop)
theorem file29_49753 : (((((p5 ∧ p4) ∧ (False ∧ p6)) ∧ ((p0 → False) → (p5 ∧ p1))) → False) ∨ ((((p3 → p3) → (False ∨ False)) ∧ ((p0 → False) ∧ (True → p2))) → False)) := by
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


variable (p0 p5 p3 p6 p1 p2 : Prop)
theorem file29_50263 : (((((True ∨ p3) → False) ∨ ((p2 ∨ True) ∨ (p0 → p1))) ∧ (((p6 → p6) ∨ (p5 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_54 : ((p6 → p6) ∨ (p5 → False)) := by
        apply Or.inl
        intro assump_11
        exact assump_11
      let assump_10 := assump_3 assump_54
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_17 =>
        cases assump_17
        case inl assump_19 =>
          have assump_55 : ((p6 → p6) ∨ (p5 → False)) := by
            apply Or.inl
            intro assump_26
            exact assump_26
          let assump_25 := assump_3 assump_55
          apply False.elim assump_25
        case inr assump_20 =>
          have assump_56 : ((p6 → p6) ∨ (p5 → False)) := by
            apply Or.inl
            intro assump_37
            exact assump_37
          let assump_36 := assump_3 assump_56
          apply False.elim assump_36
      case inr assump_18 =>
        have assump_57 : ((p6 → p6) ∨ (p5 → False)) := by
          apply Or.inl
          intro assump_48
          exact assump_48
        let assump_47 := assump_3 assump_57
        apply False.elim assump_47


variable (p7 p3 p1 p0 p5 : Prop)
theorem file29_51587 : (((((p5 ∧ p3) ∧ (p5 → False)) → ((p1 → False) ∨ (p7 → p0))) → False) → False) := by
  intro assump_1
  have assump_27 : (((p5 ∧ p3) ∧ (p5 → False)) → ((p1 → False) ∨ (p7 → p0))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_16
        have assump_28 : p5 := by
          exact assump_8
        let assump_20 := assump_7 assump_28
        apply False.elim assump_20
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p4 p1 : Prop)
theorem file29_52200 : (((((True → p4) ∨ (p1 → p4)) → ((False → False) ∨ (p4 → False))) → False) → False) := by
  intro assump_1
  have assump_21 : (((True → p4) ∨ (p1 → p4)) → ((False → False) ∨ (p4 → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      apply Or.inl
      intro assump_15
      apply False.elim assump_15
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p6 p5 p4 p0 p7 p3 : Prop)
theorem file29_52755 : (((((p6 ∨ False) ∧ (p7 ∨ p3)) → False) ∧ (((True ∨ False) ∨ (p0 → False)) → False)) → ((((p3 → False) ∧ (p4 → p7)) → ((p3 → False) → False)) → (((p0 ∧ True) ∨ (p0 ∨ p5)) → ((p5 → p4) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_1
      case intro assump_17 assump_18 =>
        have assump_57 : ((True ∨ False) ∨ (p0 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_23 := assump_18 assump_57
        apply False.elim assump_23
  case inr assump_8 =>
    cases assump_8
    case inl assump_27 =>
      cases assump_1
      case intro assump_33 assump_34 =>
        have assump_58 : ((True ∨ False) ∨ (p0 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_39 := assump_34 assump_58
        apply False.elim assump_39
    case inr assump_28 =>
      cases assump_1
      case intro assump_47 assump_48 =>
        have assump_59 : ((True ∨ False) ∨ (p0 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_53 := assump_48 assump_59
        apply False.elim assump_53


variable (p1 p5 p7 p6 p0 p4 p3 p2 : Prop)
theorem file29_54111 : (((((p2 → False) → False) → False) ∨ (((p7 ∧ p0) ∧ (True → False)) → ((p3 ∧ p2) → False))) → ((((True ∨ p3) → (True → p6)) ∨ ((p3 → False) → False)) → (((p1 ∨ True) ∨ (False ∨ p0)) ∧ ((p5 → True) ∨ (p4 → p5))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
  case inr assump_4 =>
    cases assump_1
    case inl assump_15 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_16 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
  cases assump_2
  case inl assump_21 =>
    cases assump_1
    case inl assump_25 =>
      apply Or.inl
      intro assump_29
      apply True.intro
    case inr assump_26 =>
      apply Or.inl
      intro assump_32
      apply True.intro
  case inr assump_22 =>
    cases assump_1
    case inl assump_35 =>
      apply Or.inl
      intro assump_39
      apply True.intro
    case inr assump_36 =>
      apply Or.inl
      intro assump_42
      apply True.intro


variable (p3 p6 p2 p5 p4 : Prop)
theorem file29_55348 : (((((p6 → p6) ∧ (p5 ∧ p3)) → False) ∧ (((p4 → p2) → False) ∧ ((p6 ∧ p2) ∧ (p4 → p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_30 : (p4 → p2) := by
            intro assump_24
            exact assump_13
          let assump_23 := assump_6 assump_30
          apply False.elim assump_23


variable (p1 p2 p0 p5 p7 p6 p3 : Prop)
theorem file29_55945 : (((((p3 → False) ∧ (p2 ∧ p6)) → ((p3 ∧ p1) → (p7 → p0))) → (((p3 → p3) → False) ∧ ((False → p6) → False))) → ((((p2 → p0) → False) → ((p1 ∧ p6) → (p6 → False))) → (((p5 → False) → (p7 ∧ p5)) ∧ ((p0 ∧ p3) ∨ (p0 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply And.intro
  have assump_126 : (((p3 → False) ∧ (p2 ∧ p6)) → ((p3 ∧ p1) → (p7 → p0))) := by
    intro assump_11
    intro assump_12
    intro assump_13
    cases assump_12
    case intro assump_16 assump_17 =>
      cases assump_11
      case intro assump_22 assump_23 =>
        cases assump_23
        case intro assump_26 assump_27 =>
          have assump_127 : p3 := by
            exact assump_16
          let assump_34 := assump_22 assump_127
          apply False.elim assump_34
  let assump_10 := assump_1 assump_126
  let assump_38 := And.left assump_10
  have assump_128 : (p3 → p3) := by
    intro assump_40
    exact assump_40
  let assump_39 := assump_38 assump_128
  apply False.elim assump_39
  have assump_129 : (((p3 → False) ∧ (p2 ∧ p6)) → ((p3 ∧ p1) → (p7 → p0))) := by
    intro assump_53
    intro assump_54
    intro assump_55
    cases assump_54
    case intro assump_58 assump_59 =>
      cases assump_53
      case intro assump_64 assump_65 =>
        cases assump_65
        case intro assump_68 assump_69 =>
          have assump_130 : p3 := by
            exact assump_58
          let assump_76 := assump_64 assump_130
          apply False.elim assump_76
  let assump_52 := assump_1 assump_129
  let assump_80 := And.left assump_52
  have assump_131 : (p3 → p3) := by
    intro assump_82
    exact assump_82
  let assump_81 := assump_80 assump_131
  apply False.elim assump_81
  apply Or.inr
  intro assump_92
  have assump_132 : (((p3 → False) ∧ (p2 ∧ p6)) → ((p3 ∧ p1) → (p7 → p0))) := by
    intro assump_97
    intro assump_98
    intro assump_99
    cases assump_98
    case intro assump_102 assump_103 =>
      cases assump_97
      case intro assump_108 assump_109 =>
        cases assump_109
        case intro assump_112 assump_113 =>
          exact assump_92
  let assump_96 := assump_1 assump_132
  let assump_118 := And.left assump_96
  have assump_133 : (p3 → p3) := by
    intro assump_120
    exact assump_120
  let assump_119 := assump_118 assump_133
  apply False.elim assump_119


variable (p4 p0 p5 p6 : Prop)
theorem file29_58334 : (((((p6 → p4) ∧ (p0 ∨ p0)) ∨ ((p4 → False) → False)) ∧ (((False → False) ∨ (False ∨ p5)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          have assump_45 : ((False → False) ∨ (False ∨ p5)) := by
            apply Or.inl
            intro assump_17
            apply False.elim assump_17
          let assump_16 := assump_3 assump_45
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_46 : ((False → False) ∨ (False ∨ p5)) := by
            apply Or.inl
            intro assump_28
            apply False.elim assump_28
          let assump_27 := assump_3 assump_46
          apply False.elim assump_27
    case inr assump_5 =>
      have assump_47 : ((False → False) ∨ (False ∨ p5)) := by
        apply Or.inl
        intro assump_39
        apply False.elim assump_39
      let assump_38 := assump_3 assump_47
      apply False.elim assump_38


variable (p3 p1 p5 p0 : Prop)
theorem file29_59480 : ((((((p5 → False) → False) → False) → (((p1 ∧ p3) ∨ (True → p5)) → False)) ∧ ((((p5 → p0) ∧ (False → p3)) → ((p5 ∧ True) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p5 → p0) ∧ (False → p3)) → ((p5 ∧ True) → (False → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p2 p6 p4 p3 p7 p5 p1 : Prop)
theorem file29_60034 : ((((((p5 → p6) → False) ∧ ((p7 ∧ p6) ∧ (p3 → p2))) → (((p1 ∧ p4) ∨ (p2 ∨ p2)) → False)) → False) → False) := by
  intro assump_33
  have assump_128 : ((((p5 → p6) → False) ∧ ((p7 ∧ p6) ∧ (p3 → p2))) → (((p1 ∧ p4) ∨ (p2 ∨ p2)) → False)) := by
    intro assump_37
    intro assump_38
    cases assump_38
    case inl assump_39 =>
      cases assump_39
      case intro assump_41 assump_42 =>
        cases assump_37
        case intro assump_47 assump_48 =>
          cases assump_48
          case intro assump_51 assump_52 =>
            cases assump_51
            case intro assump_53 assump_54 =>
              have assump_129 : (p5 → p6) := by
                intro assump_65
                exact assump_54
              let assump_64 := assump_47 assump_129
              apply False.elim assump_64
    case inr assump_40 =>
      cases assump_40
      case inl assump_71 =>
        cases assump_37
        case intro assump_75 assump_76 =>
          cases assump_76
          case intro assump_79 assump_80 =>
            cases assump_79
            case intro assump_81 assump_82 =>
              have assump_130 : (p5 → p6) := by
                intro assump_93
                exact assump_82
              let assump_92 := assump_75 assump_130
              apply False.elim assump_92
      case inr assump_72 =>
        cases assump_37
        case intro assump_101 assump_102 =>
          cases assump_102
          case intro assump_105 assump_106 =>
            cases assump_105
            case intro assump_107 assump_108 =>
              have assump_131 : (p5 → p6) := by
                intro assump_119
                exact assump_108
              let assump_118 := assump_101 assump_131
              apply False.elim assump_118
  let assump_36 := assump_33 assump_128
  apply False.elim assump_36


variable (p1 p7 p4 p0 p2 p3 p5 : Prop)
theorem file29_61918 : (((((p5 → False) → (p4 ∧ p4)) ∨ ((False → False) → False)) → (((False ∧ p3) → False) ∨ ((p0 ∨ True) → False))) ∨ ((((p7 → p2) → False) → ((p7 → p4) ∧ (p7 ∧ p5))) ∨ (((p1 → False) → (p1 → False)) ∨ ((p1 ∧ p3) → (p4 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  case inr assump_3 =>
    apply Or.inl
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply False.elim assump_14


variable (p2 p1 p7 p4 p0 p5 p3 : Prop)
theorem file29_62557 : ((((((p4 → p2) ∨ (True → p1)) ∧ ((False → p1) → False)) → (((False ∧ p3) → (False → p1)) ∨ ((p0 ∧ True) → False))) → ((((p7 → False) ∧ (p7 ∧ p2)) → ((True ∧ p2) → (p5 ∧ p3))) → False)) → False) := by
  intro assump_1
  have assump_76 : ((((p4 → p2) ∨ (True → p1)) ∧ ((False → p1) → False)) → (((False ∧ p3) → (False → p1)) ∨ ((p0 ∧ True) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_14
        intro assump_15
        apply False.elim assump_15
      case inr assump_9 =>
        apply Or.inl
        intro assump_22
        intro assump_23
        apply False.elim assump_23
  let assump_4 := assump_1 assump_76
  have assump_77 : (((p7 → False) ∧ (p7 ∧ p2)) → ((True ∧ p2) → (p5 ∧ p3))) := by
    intro assump_27
    intro assump_28
    apply And.intro
    cases assump_28
    case intro assump_29 assump_30 =>
      cases assump_27
      case intro assump_35 assump_36 =>
        cases assump_36
        case intro assump_39 assump_40 =>
          have assump_78 : p7 := by
            exact assump_39
          let assump_47 := assump_35 assump_78
          apply False.elim assump_47
    cases assump_28
    case intro assump_51 assump_52 =>
      cases assump_27
      case intro assump_57 assump_58 =>
        cases assump_58
        case intro assump_61 assump_62 =>
          have assump_79 : p7 := by
            exact assump_61
          let assump_69 := assump_57 assump_79
          apply False.elim assump_69
  let assump_26 := assump_4 assump_77
  apply False.elim assump_26


variable (p5 p1 p7 p3 p4 p0 : Prop)
theorem file29_64243 : (((((True ∨ p4) ∨ (p0 → False)) ∨ ((p4 ∧ p5) ∧ (p3 → False))) ∧ (((p7 ∨ p1) ∨ (p1 → p0)) ∧ ((True ∨ p4) ∧ (p3 → False)))) → ((((p7 ∨ False) → (False → p0)) ∧ ((p4 ∧ False) → False)) ∨ (((p4 → False) ∨ (p1 ∧ p4)) ∧ ((False → p7) → (p5 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_12 assump_13 =>
            cases assump_12
            case inl assump_14 =>
              cases assump_14
              case inl assump_16 =>
                cases assump_13
                case intro assump_20 assump_21 =>
                  cases assump_20
                  case inl assump_22 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_28
                    intro assump_29
                    apply False.elim assump_29
                    intro assump_32
                    cases assump_32
                    case intro assump_33 assump_34 =>
                      apply False.elim assump_34
                  case inr assump_23 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_43
                    intro assump_44
                    apply False.elim assump_44
                    intro assump_47
                    cases assump_47
                    case intro assump_48 assump_49 =>
                      apply False.elim assump_49
              case inr assump_17 =>
                cases assump_13
                case intro assump_56 assump_57 =>
                  cases assump_56
                  case inl assump_58 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_64
                    intro assump_65
                    apply False.elim assump_65
                    intro assump_68
                    cases assump_68
                    case intro assump_69 assump_70 =>
                      apply False.elim assump_70
                  case inr assump_59 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_79
                    intro assump_80
                    apply False.elim assump_80
                    intro assump_83
                    cases assump_83
                    case intro assump_84 assump_85 =>
                      apply False.elim assump_85
            case inr assump_15 =>
              cases assump_13
              case intro assump_92 assump_93 =>
                cases assump_92
                case inl assump_94 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_100
                  intro assump_101
                  apply False.elim assump_101
                  intro assump_104
                  cases assump_104
                  case intro assump_105 assump_106 =>
                    apply False.elim assump_106
                case inr assump_95 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_115
                  intro assump_116
                  apply False.elim assump_116
                  intro assump_119
                  cases assump_119
                  case intro assump_120 assump_121 =>
                    apply False.elim assump_121
        case inr assump_9 =>
          cases assump_3
          case intro assump_128 assump_129 =>
            cases assump_128
            case inl assump_130 =>
              cases assump_130
              case inl assump_132 =>
                cases assump_129
                case intro assump_136 assump_137 =>
                  cases assump_136
                  case inl assump_138 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_144
                    intro assump_145
                    apply False.elim assump_145
                    intro assump_148
                    cases assump_148
                    case intro assump_149 assump_150 =>
                      apply False.elim assump_150
                  case inr assump_139 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_159
                    intro assump_160
                    apply False.elim assump_160
                    intro assump_163
                    cases assump_163
                    case intro assump_164 assump_165 =>
                      apply False.elim assump_165
              case inr assump_133 =>
                cases assump_129
                case intro assump_172 assump_173 =>
                  cases assump_172
                  case inl assump_174 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_180
                    intro assump_181
                    apply False.elim assump_181
                    intro assump_184
                    cases assump_184
                    case intro assump_185 assump_186 =>
                      apply False.elim assump_186
                  case inr assump_175 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_195
                    intro assump_196
                    apply False.elim assump_196
                    intro assump_199
                    cases assump_199
                    case intro assump_200 assump_201 =>
                      apply False.elim assump_201
            case inr assump_131 =>
              cases assump_129
              case intro assump_208 assump_209 =>
                cases assump_208
                case inl assump_210 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_216
                  intro assump_217
                  apply False.elim assump_217
                  intro assump_220
                  cases assump_220
                  case intro assump_221 assump_222 =>
                    apply False.elim assump_222
                case inr assump_211 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_231
                  intro assump_232
                  apply False.elim assump_232
                  intro assump_235
                  cases assump_235
                  case intro assump_236 assump_237 =>
                    apply False.elim assump_237
      case inr assump_7 =>
        cases assump_3
        case intro assump_244 assump_245 =>
          cases assump_244
          case inl assump_246 =>
            cases assump_246
            case inl assump_248 =>
              cases assump_245
              case intro assump_252 assump_253 =>
                cases assump_252
                case inl assump_254 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_260
                  intro assump_261
                  apply False.elim assump_261
                  intro assump_264
                  cases assump_264
                  case intro assump_265 assump_266 =>
                    apply False.elim assump_266
                case inr assump_255 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_275
                  intro assump_276
                  apply False.elim assump_276
                  intro assump_279
                  cases assump_279
                  case intro assump_280 assump_281 =>
                    apply False.elim assump_281
            case inr assump_249 =>
              cases assump_245
              case intro assump_288 assump_289 =>
                cases assump_288
                case inl assump_290 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_296
                  intro assump_297
                  apply False.elim assump_297
                  intro assump_300
                  cases assump_300
                  case intro assump_301 assump_302 =>
                    apply False.elim assump_302
                case inr assump_291 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_311
                  intro assump_312
                  apply False.elim assump_312
                  intro assump_315
                  cases assump_315
                  case intro assump_316 assump_317 =>
                    apply False.elim assump_317
          case inr assump_247 =>
            cases assump_245
            case intro assump_324 assump_325 =>
              cases assump_324
              case inl assump_326 =>
                apply Or.inl
                apply And.intro
                intro assump_332
                intro assump_333
                apply False.elim assump_333
                intro assump_336
                cases assump_336
                case intro assump_337 assump_338 =>
                  apply False.elim assump_338
              case inr assump_327 =>
                apply Or.inl
                apply And.intro
                intro assump_347
                intro assump_348
                apply False.elim assump_348
                intro assump_351
                cases assump_351
                case intro assump_352 assump_353 =>
                  apply False.elim assump_353
    case inr assump_5 =>
      cases assump_5
      case intro assump_358 assump_359 =>
        cases assump_358
        case intro assump_360 assump_361 =>
          cases assump_3
          case intro assump_368 assump_369 =>
            cases assump_368
            case inl assump_370 =>
              cases assump_370
              case inl assump_372 =>
                cases assump_369
                case intro assump_376 assump_377 =>
                  cases assump_376
                  case inl assump_378 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_384
                    intro assump_385
                    apply False.elim assump_385
                    intro assump_388
                    cases assump_388
                    case intro assump_389 assump_390 =>
                      apply False.elim assump_390
                  case inr assump_379 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_399
                    intro assump_400
                    apply False.elim assump_400
                    intro assump_403
                    cases assump_403
                    case intro assump_404 assump_405 =>
                      apply False.elim assump_405
              case inr assump_373 =>
                cases assump_369
                case intro assump_412 assump_413 =>
                  cases assump_412
                  case inl assump_414 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_420
                    intro assump_421
                    apply False.elim assump_421
                    intro assump_424
                    cases assump_424
                    case intro assump_425 assump_426 =>
                      apply False.elim assump_426
                  case inr assump_415 =>
                    apply Or.inl
                    apply And.intro
                    intro assump_435
                    intro assump_436
                    apply False.elim assump_436
                    intro assump_439
                    cases assump_439
                    case intro assump_440 assump_441 =>
                      apply False.elim assump_441
            case inr assump_371 =>
              cases assump_369
              case intro assump_448 assump_449 =>
                cases assump_448
                case inl assump_450 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_456
                  intro assump_457
                  apply False.elim assump_457
                  intro assump_460
                  cases assump_460
                  case intro assump_461 assump_462 =>
                    apply False.elim assump_462
                case inr assump_451 =>
                  apply Or.inl
                  apply And.intro
                  intro assump_471
                  intro assump_472
                  apply False.elim assump_472
                  intro assump_475
                  cases assump_475
                  case intro assump_476 assump_477 =>
                    apply False.elim assump_477


variable (p0 p1 p6 p3 p2 p5 : Prop)
theorem file29_77013 : (((((p6 ∨ p3) → False) → ((True ∨ p6) ∨ (False ∨ p2))) ∨ (((True ∧ p5) → (True ∧ p0)) ∧ ((p6 → p1) ∧ (True → False)))) ∨ ((((p3 → False) ∨ (p2 → p1)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p1 p3 p7 : Prop)
theorem file29_77335 : (((((True → False) → False) ∧ ((False ∧ p7) ∧ (p1 → p1))) ∧ (((True → False) → (p7 ∨ p3)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p5 p4 p0 p2 : Prop)
theorem file29_77788 : (((((False → p5) ∧ (p4 ∧ p2)) → ((p0 ∧ p4) → (True ∧ True))) → False) → False) := by
  intro assump_1
  have assump_10 : (((False → p5) ∧ (p4 ∧ p2)) → ((p0 ∧ p4) → (True ∧ True))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p0 p1 p7 p6 p4 p2 : Prop)
theorem file29_78199 : ((((((p6 ∧ True) → (p4 → p6)) ∨ ((p7 ∨ True) ∧ (p6 ∧ p7))) → (((p1 → p0) → (False → False)) ∨ ((p7 → p2) → (False ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_45 : ((((p6 ∧ True) → (p4 → p6)) ∨ ((p7 ∨ True) ∧ (p6 ∧ p7))) → (((p1 → p0) → (False → False)) ∨ ((p7 → p2) → (False ∨ p4)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case intro assump_20 assump_21 =>
            apply Or.inl
            intro assump_26
            intro assump_27
            apply False.elim assump_27
        case inr assump_17 =>
          cases assump_15
          case intro assump_32 assump_33 =>
            apply Or.inl
            intro assump_38
            intro assump_39
            apply False.elim assump_39
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


variable (p3 p2 p7 p4 p0 p1 p6 p5 : Prop)
theorem file29_79349 : (((((p2 ∨ p2) → (p6 ∨ p7)) ∧ ((p2 ∧ p0) → (p7 ∨ p5))) → False) → ((((False ∨ p3) → False) ∨ ((p3 → False) ∨ (p4 ∨ False))) → (((p5 → p1) ∨ (p7 → False)) → ((p4 → True) ∨ (True → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      apply Or.inl
      intro assump_14
      apply True.intro
    case inr assump_9 =>
      cases assump_9
      case inl assump_15 =>
        apply Or.inl
        intro assump_21
        apply True.intro
      case inr assump_16 =>
        cases assump_16
        case inl assump_22 =>
          apply Or.inl
          intro assump_28
          apply True.intro
        case inr assump_23 =>
          apply False.elim assump_23
  case inr assump_5 =>
    cases assump_2
    case inl assump_33 =>
      apply Or.inl
      intro assump_39
      apply True.intro
    case inr assump_34 =>
      cases assump_34
      case inl assump_40 =>
        apply Or.inl
        intro assump_46
        apply True.intro
      case inr assump_41 =>
        cases assump_41
        case inl assump_47 =>
          apply Or.inl
          intro assump_53
          apply True.intro
        case inr assump_48 =>
          apply False.elim assump_48


variable (p3 p4 p2 p7 : Prop)
theorem file29_80669 : (((((p4 → p4) → False) ∨ ((p4 → False) ∧ (p7 ∨ False))) → (((p7 ∨ True) → False) → ((False ∨ True) → (p4 → False)))) ∨ ((((p4 ∨ p3) → False) → ((p4 → True) → (p2 ∨ p7))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    apply False.elim assump_7
  case inr assump_8 =>
    cases assump_1
    case inl assump_15 =>
      have assump_41 : (p4 → p4) := by
        intro assump_20
        exact assump_20
      let assump_19 := assump_15 assump_41
      apply False.elim assump_19
    case inr assump_16 =>
      cases assump_16
      case intro assump_26 assump_27 =>
        cases assump_27
        case inl assump_30 =>
          have assump_42 : p4 := by
            exact assump_4
          let assump_35 := assump_26 assump_42
          apply False.elim assump_35
        case inr assump_31 =>
          apply False.elim assump_31


variable (p0 p7 p6 p1 p2 p3 p5 p4 : Prop)
theorem file29_81661 : (((((True → False) ∨ (False → False)) ∧ ((p5 ∧ p3) ∧ (p2 ∧ p4))) → (((p1 → p6) ∨ (False ∨ p4)) → False)) → ((((p1 → False) ∧ (p7 ∧ p7)) ∧ ((p1 ∨ p6) → False)) → (((p6 → True) ∨ (p7 ∨ True)) ∨ ((p0 → False) ∧ (p2 → p7))))) := by
  intro assump_33
  intro assump_34
  cases assump_34
  case intro assump_35 assump_36 =>
    cases assump_35
    case intro assump_37 assump_38 =>
      cases assump_38
      case intro assump_41 assump_42 =>
        apply Or.inl
        apply Or.inl
        intro assump_51
        apply True.intro


variable (p3 p0 p2 p6 p4 p1 : Prop)
theorem file29_82250 : (((((False → False) → False) → ((p0 ∨ p6) ∧ (p3 → False))) → False) → ((((p0 ∨ False) ∧ (p6 ∨ p4)) ∧ ((p1 → False) ∧ (p3 → False))) ∧ (((p4 → p4) → False) ∧ ((p6 ∧ p6) ∧ (p1 ∨ p2))))) := by
  intro assump_10
  apply And.intro
  apply And.intro
  apply And.intro
  have assump_244 : (((False → False) → False) → ((p0 ∨ p6) ∧ (p3 → False))) := by
    intro assump_14
    apply And.intro
    have assump_245 : (False → False) := by
      intro assump_18
      apply False.elim assump_18
    let assump_17 := assump_14 assump_245
    apply False.elim assump_17
    intro assump_24
    have assump_246 : (False → False) := by
      intro assump_30
      apply False.elim assump_30
    let assump_29 := assump_14 assump_246
    apply False.elim assump_29
  let assump_13 := assump_10 assump_244
  apply False.elim assump_13
  have assump_247 : (((False → False) → False) → ((p0 ∨ p6) ∧ (p3 → False))) := by
    intro assump_42
    apply And.intro
    have assump_248 : (False → False) := by
      intro assump_46
      apply False.elim assump_46
    let assump_45 := assump_42 assump_248
    apply False.elim assump_45
    intro assump_52
    have assump_249 : (False → False) := by
      intro assump_58
      apply False.elim assump_58
    let assump_57 := assump_42 assump_249
    apply False.elim assump_57
  let assump_41 := assump_10 assump_247
  apply False.elim assump_41
  apply And.intro
  intro assump_67
  have assump_250 : (((False → False) → False) → ((p0 ∨ p6) ∧ (p3 → False))) := by
    intro assump_73
    apply And.intro
    have assump_251 : (False → False) := by
      intro assump_77
      apply False.elim assump_77
    let assump_76 := assump_73 assump_251
    apply False.elim assump_76
    intro assump_83
    have assump_252 : (False → False) := by
      intro assump_89
      apply False.elim assump_89
    let assump_88 := assump_73 assump_252
    apply False.elim assump_88
  let assump_72 := assump_10 assump_250
  apply False.elim assump_72
  intro assump_98
  have assump_253 : (((False → False) → False) → ((p0 ∨ p6) ∧ (p3 → False))) := by
    intro assump_104
    apply And.intro
    have assump_254 : (False → False) := by
      intro assump_108
      apply False.elim assump_108
    let assump_107 := assump_104 assump_254
    apply False.elim assump_107
    intro assump_114
    have assump_255 : (False → False) := by
      intro assump_120
      apply False.elim assump_120
    let assump_119 := assump_104 assump_255
    apply False.elim assump_119
  let assump_103 := assump_10 assump_253
  apply False.elim assump_103
  apply And.intro
  intro assump_129
  have assump_256 : (((False → False) → False) → ((p0 ∨ p6) ∧ (p3 → False))) := by
    intro assump_135
    apply And.intro
    have assump_257 : (False → False) := by
      intro assump_139
      apply False.elim assump_139
    let assump_138 := assump_135 assump_257
    apply False.elim assump_138
    intro assump_145
    have assump_258 : (False → False) := by
      intro assump_151
      apply False.elim assump_151
    let assump_150 := assump_135 assump_258
    apply False.elim assump_150
  let assump_134 := assump_10 assump_256
  apply False.elim assump_134
  apply And.intro
  apply And.intro
  have assump_259 : (((False → False) → False) → ((p0 ∨ p6) ∧ (p3 → False))) := by
    intro assump_163
    apply And.intro
    have assump_260 : (False → False) := by
      intro assump_167
      apply False.elim assump_167
    let assump_166 := assump_163 assump_260
    apply False.elim assump_166
    intro assump_173
    have assump_261 : (False → False) := by
      intro assump_179
      apply False.elim assump_179
    let assump_178 := assump_163 assump_261
    apply False.elim assump_178
  let assump_162 := assump_10 assump_259
  apply False.elim assump_162
  have assump_262 : (((False → False) → False) → ((p0 ∨ p6) ∧ (p3 → False))) := by
    intro assump_191
    apply And.intro
    have assump_263 : (False → False) := by
      intro assump_195
      apply False.elim assump_195
    let assump_194 := assump_191 assump_263
    apply False.elim assump_194
    intro assump_201
    have assump_264 : (False → False) := by
      intro assump_207
      apply False.elim assump_207
    let assump_206 := assump_191 assump_264
    apply False.elim assump_206
  let assump_190 := assump_10 assump_262
  apply False.elim assump_190
  have assump_265 : (((False → False) → False) → ((p0 ∨ p6) ∧ (p3 → False))) := by
    intro assump_219
    apply And.intro
    have assump_266 : (False → False) := by
      intro assump_223
      apply False.elim assump_223
    let assump_222 := assump_219 assump_266
    apply False.elim assump_222
    intro assump_229
    have assump_267 : (False → False) := by
      intro assump_235
      apply False.elim assump_235
    let assump_234 := assump_219 assump_267
    apply False.elim assump_234
  let assump_218 := assump_10 assump_265
  apply False.elim assump_218


variable (p5 p0 p6 p2 p3 p4 : Prop)
theorem file29_87217 : (((((False ∧ p6) → False) → ((p3 ∧ p2) → False)) → (((False ∨ False) ∧ (p5 → p4)) → ((p0 ∨ p6) ∧ (p3 → False)))) ∨ ((((p0 → False) ∨ (p6 ∧ p6)) ∧ ((True → p3) → (p5 → p0))) → (((p6 → False) ∧ (p4 → False)) → ((p5 ∨ p3) ∧ (p3 ∧ p0))))) := by
  apply Or.inl
  intro assump_15
  intro assump_16
  apply And.intro
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case inl assump_19 =>
      apply False.elim assump_19
    case inr assump_20 =>
      apply False.elim assump_20
  intro assump_25
  cases assump_16
  case intro assump_28 assump_29 =>
    cases assump_28
    case inl assump_30 =>
      apply False.elim assump_30
    case inr assump_31 =>
      apply False.elim assump_31


variable (p5 p6 p2 p4 p3 p7 p0 : Prop)
theorem file29_87992 : (((((p6 → p5) ∧ (p3 ∧ False)) → ((p7 ∨ p3) → False)) ∨ (((p7 → p5) ∧ (p2 → False)) → False)) ∨ ((((p4 → False) → False) → ((p4 → p7) → (p0 → p3))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case inl assump_7 =>
    cases assump_5
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
  case inr assump_8 =>
    cases assump_5
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        apply False.elim assump_28


variable (p5 p4 p3 p7 p2 p0 : Prop)
theorem file29_88650 : ((((((p4 → p3) → False) ∧ ((p0 → False) → (p4 ∧ p7))) ∨ (((p2 → False) → False) ∧ ((p7 → p2) → (p0 ∧ p5)))) ∧ ((((p0 ∧ p4) ∧ (p2 ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_60 : (((p0 ∧ p4) ∧ (p2 ∧ False)) → False) := by
          intro assump_15
          cases assump_15
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                apply False.elim assump_25
        let assump_14 := assump_3 assump_60
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case intro assump_33 assump_34 =>
        have assump_61 : (((p0 ∧ p4) ∧ (p2 ∧ False)) → False) := by
          intro assump_42
          cases assump_42
          case intro assump_43 assump_44 =>
            cases assump_43
            case intro assump_45 assump_46 =>
              cases assump_44
              case intro assump_51 assump_52 =>
                apply False.elim assump_52
        let assump_41 := assump_3 assump_61
        apply False.elim assump_41


variable (p3 p4 p7 p1 : Prop)
theorem file29_90010 : (((((True ∧ True) ∨ (True → False)) → False) → (((p3 ∧ p7) → (p3 → p3)) → False)) ∨ ((((False ∧ True) ∨ (p1 ∧ p4)) ∨ ((p4 ∨ p7) → False)) ∨ (((p3 → False) → (p1 → True)) ∨ ((True → False) ∧ (False → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : ((True ∧ True) ∨ (True → False)) := by
    apply Or.inl
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p0 p4 p6 p2 p5 p7 p1 p3 : Prop)
theorem file29_90543 : (((((p0 → True) → (p0 ∧ p4)) ∨ ((True → True) ∨ (p2 → p1))) → False) → ((((p6 ∨ p2) → False) ∧ ((p7 ∨ p5) ∨ (False ∧ p6))) → (((p7 → False) ∨ (p0 ∨ p2)) → ((False ∧ p3) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p2 p3 p1 p5 p4 p6 p0 p7 : Prop)
theorem file29_90945 : ((((((p6 ∨ True) → (p5 → False)) ∧ ((p0 ∨ p3) ∧ (False → False))) → (((p4 ∨ p7) → False) → ((p1 ∨ p5) → (p6 → False)))) ∧ ((((p2 ∨ True) ∨ (p1 → p1)) ∧ ((p2 ∨ False) ∧ (p5 → False))) ∧ (((p4 ∧ p0) ∨ (p2 ∨ True)) → False))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_21
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_26
        case inl assump_28 =>
          cases assump_28
          case inl assump_30 =>
            cases assump_27
            case intro assump_34 assump_35 =>
              cases assump_34
              case inl assump_36 =>
                have assump_86 : ((p4 ∧ p0) ∨ (p2 ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  exact assump_36
                let assump_44 := assump_25 assump_86
                apply False.elim assump_44
              case inr assump_37 =>
                apply False.elim assump_37
          case inr assump_31 =>
            cases assump_27
            case intro assump_52 assump_53 =>
              cases assump_52
              case inl assump_54 =>
                have assump_87 : ((p4 ∧ p0) ∨ (p2 ∨ True)) := by
                  apply Or.inr
                  apply Or.inl
                  exact assump_54
                let assump_62 := assump_25 assump_87
                apply False.elim assump_62
              case inr assump_55 =>
                apply False.elim assump_55
        case inr assump_29 =>
          cases assump_27
          case intro assump_70 assump_71 =>
            cases assump_70
            case inl assump_72 =>
              have assump_88 : ((p4 ∧ p0) ∨ (p2 ∨ True)) := by
                apply Or.inr
                apply Or.inl
                exact assump_72
              let assump_80 := assump_25 assump_88
              apply False.elim assump_80
            case inr assump_73 =>
              apply False.elim assump_73


variable (p3 p7 p6 p1 p2 : Prop)
theorem file29_93010 : ((((((True → False) → False) ∨ ((p1 → p1) ∨ (p2 → False))) ∨ (((p2 ∨ p6) → (p7 → False)) ∨ ((True → False) ∧ (False ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True → False) → False) ∨ ((p1 → p1) ∨ (p2 → False))) ∨ (((p2 ∨ p6) → (p7 → False)) ∨ ((True → False) ∧ (False ∧ p3)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p2 p6 p5 p0 p3 p7 : Prop)
theorem file29_93629 : (((((True ∧ p1) ∧ (p7 ∧ p0)) → ((p5 → p0) ∧ (p7 → False))) ∧ (((p0 ∨ p5) → (False → p7)) ∧ ((False ∧ p3) ∧ (p0 → p3)))) → ((((p3 ∧ p5) → False) ∧ ((p5 ∨ True) → (False ∨ True))) ∨ (((p2 ∨ p6) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p0 p2 p5 p1 p3 : Prop)
theorem file29_94191 : ((((((p2 ∧ p3) ∧ (p2 → False)) → ((True → False) → (p1 → False))) ∨ (((p0 ∨ p1) → False) ∨ ((False → False) ∧ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p2 ∧ p3) ∧ (p2 → False)) → ((True → False) → (p1 → False))) ∨ (((p0 ∨ p1) → False) ∨ ((False → False) ∧ (p5 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_30 : p2 := by
          exact assump_14
        let assump_22 := assump_13 assump_30
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p6 p4 p5 p7 p1 p0 : Prop)
theorem file29_94965 : (((((p4 → p6) ∨ (True ∨ p0)) → ((p7 → False) → False)) ∧ (((True → False) → (p6 → False)) → False)) → ((((p5 ∧ True) ∨ (p0 → p1)) ∨ ((p5 → True) ∧ (False → p4))) ∨ (((p5 ∨ p4) → (p4 → False)) ∧ ((True → p0) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_8
    have assump_26 : ((True → False) → (p6 → False)) := by
      intro assump_13
      intro assump_14
      have assump_27 : True := by
        apply True.intro
      let assump_19 := assump_13 assump_27
      apply False.elim assump_19
    let assump_12 := assump_3 assump_26
    apply False.elim assump_12


variable (p2 p4 p0 p7 : Prop)
theorem file29_95691 : ((((((p4 → p2) ∨ (p2 ∨ p4)) ∨ ((p0 ∧ p7) → False)) → False) ∧ ((((p4 ∨ False) → False) → False) ∧ (((False → False) ∨ (p0 ∧ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((False → False) ∨ (p0 ∧ p7)) := by
        apply Or.inl
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p1 p2 p6 p4 p0 p7 : Prop)
theorem file29_96243 : ((((((False → True) ∨ (p1 ∧ p1)) ∨ ((p0 → False) ∨ (False ∧ p1))) ∨ (((p6 → False) ∨ (p7 → False)) ∨ ((p1 → p2) ∧ (False ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_9 : ((((False → True) ∨ (p1 ∧ p1)) ∨ ((p0 → False) ∨ (False ∧ p1))) ∨ (((p6 → False) ∨ (p7 → False)) ∨ ((p1 → p2) ∧ (False ∧ p4)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p6 p5 p4 p2 p0 p1 : Prop)
theorem file29_96781 : (((((p5 → False) → (False → True)) → ((p6 ∧ p4) ∧ (True ∧ p0))) → False) → ((((True → False) → (True ∧ p6)) ∨ ((False ∧ p2) → (p5 ∧ p1))) ∨ (((True ∧ p0) → False) ∧ ((False → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply And.intro
  apply True.intro
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p0 p4 p5 p6 p2 p3 p1 p7 : Prop)
theorem file29_97264 : (((((p5 → False) → False) → ((p2 ∨ False) → False)) ∨ (((p6 ∧ p0) ∧ (p7 ∨ p7)) ∧ ((p6 → p7) ∧ (p5 ∧ p3)))) → ((((p5 → p2) ∧ (False ∧ p0)) ∧ ((p4 ∨ p5) → (p3 → p1))) → (((True → False) ∨ (p5 ∨ p1)) ∧ ((False → False) ∧ (p3 ∨ p7))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
  apply And.intro
  intro assump_13
  apply False.elim assump_13
  cases assump_2
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_19
      case intro assump_22 assump_23 =>
        apply False.elim assump_22


variable (p1 p7 p4 p5 p0 p2 p3 : Prop)
theorem file29_98090 : ((((((p2 → p0) ∧ (p1 ∨ False)) → ((p1 → False) ∧ (p1 → False))) ∧ (((p0 ∨ p5) → False) ∧ ((p1 → p1) → False))) ∧ ((((p4 ∨ p7) ∨ (False ∧ True)) ∧ ((p3 → p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_24 : (p1 → p1) := by
          intro assump_18
          exact assump_18
        let assump_17 := assump_9 assump_24
        apply False.elim assump_17


variable (p6 p5 p2 p0 p4 p1 p3 p7 : Prop)
theorem file29_98702 : (((((False ∧ p3) → (p2 ∧ p4)) → False) → (((p5 → p2) → (p5 ∧ False)) ∧ ((p1 ∧ p7) ∧ (p5 → p7)))) ∨ ((((p0 → p6) → False) ∧ ((p6 → p3) ∧ (p2 → p6))) ∧ (((p7 → False) → (p3 ∧ p2)) ∧ ((p2 ∧ p3) ∧ (True → p0))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  have assump_85 : ((False ∧ p3) → (p2 ∧ p4)) := by
    intro assump_8
    apply And.intro
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
    cases assump_8
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  let assump_7 := assump_1 assump_85
  apply False.elim assump_7
  have assump_86 : ((False ∧ p3) → (p2 ∧ p4)) := by
    intro assump_25
    apply And.intro
    cases assump_25
    case intro assump_26 assump_27 =>
      apply False.elim assump_26
    cases assump_25
    case intro assump_30 assump_31 =>
      apply False.elim assump_30
  let assump_24 := assump_1 assump_86
  apply False.elim assump_24
  apply And.intro
  apply And.intro
  have assump_87 : ((False ∧ p3) → (p2 ∧ p4)) := by
    intro assump_40
    apply And.intro
    cases assump_40
    case intro assump_41 assump_42 =>
      apply False.elim assump_41
    cases assump_40
    case intro assump_45 assump_46 =>
      apply False.elim assump_45
  let assump_39 := assump_1 assump_87
  apply False.elim assump_39
  have assump_88 : ((False ∧ p3) → (p2 ∧ p4)) := by
    intro assump_55
    apply And.intro
    cases assump_55
    case intro assump_56 assump_57 =>
      apply False.elim assump_56
    cases assump_55
    case intro assump_60 assump_61 =>
      apply False.elim assump_60
  let assump_54 := assump_1 assump_88
  apply False.elim assump_54
  intro assump_67
  have assump_89 : ((False ∧ p3) → (p2 ∧ p4)) := by
    intro assump_73
    apply And.intro
    cases assump_73
    case intro assump_74 assump_75 =>
      apply False.elim assump_74
    cases assump_73
    case intro assump_78 assump_79 =>
      apply False.elim assump_78
  let assump_72 := assump_1 assump_89
  apply False.elim assump_72


variable (p7 p1 p3 p0 p2 p5 : Prop)
theorem file29_100814 : (((((False ∧ p7) ∧ (False → False)) ∨ ((p5 ∨ False) → False)) → (((p7 ∨ p3) ∧ (False ∨ p1)) ∨ ((p7 ∧ p0) ∨ (p2 → p2)))) ∨ ((((p0 → False) → (True ∨ False)) ∨ ((p7 ∨ p3) → False)) → False)) := by
  apply Or.inl
  intro assump_23
  cases assump_23
  case inl assump_24 =>
    cases assump_24
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        apply False.elim assump_28
  case inr assump_25 =>
    apply Or.inr
    apply Or.inr
    intro assump_34
    exact assump_34


variable (p1 p5 p4 p0 p6 p2 p7 : Prop)
theorem file29_101400 : (((((p4 ∨ p6) → (p5 → True)) ∨ ((p6 → p1) ∧ (True → False))) → False) → ((((p5 → p4) ∧ (p4 ∨ p0)) ∧ ((p1 → False) → (p0 ∨ p0))) → (((p6 ∨ p2) ∧ (True ∨ p7)) ∧ ((p6 → False) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        have assump_90 : (((p4 ∨ p6) → (p5 → True)) ∨ ((p6 → p1) ∧ (True → False))) := by
          apply Or.inl
          intro assump_18
          intro assump_19
          apply True.intro
        let assump_17 := assump_1 assump_90
        apply False.elim assump_17
      case inr assump_10 =>
        have assump_91 : (((p4 ∨ p6) → (p5 → True)) ∨ ((p6 → p1) ∧ (True → False))) := by
          apply Or.inl
          intro assump_30
          intro assump_31
          apply True.intro
        let assump_29 := assump_1 assump_91
        apply False.elim assump_29
  cases assump_2
  case intro assump_35 assump_36 =>
    cases assump_35
    case intro assump_37 assump_38 =>
      cases assump_38
      case inl assump_41 =>
        apply Or.inl
        apply True.intro
      case inr assump_42 =>
        apply Or.inl
        apply True.intro
  intro assump_55
  cases assump_2
  case intro assump_58 assump_59 =>
    cases assump_58
    case intro assump_60 assump_61 =>
      cases assump_61
      case inl assump_64 =>
        have assump_92 : (((p4 ∨ p6) → (p5 → True)) ∨ ((p6 → p1) ∧ (True → False))) := by
          apply Or.inl
          intro assump_73
          intro assump_74
          apply True.intro
        let assump_72 := assump_1 assump_92
        apply False.elim assump_72
      case inr assump_65 =>
        have assump_93 : (((p4 ∨ p6) → (p5 → True)) ∨ ((p6 → p1) ∧ (True → False))) := by
          apply Or.inl
          intro assump_85
          intro assump_86
          apply True.intro
        let assump_84 := assump_1 assump_93
        apply False.elim assump_84


variable (p5 p0 p3 p1 p4 p2 p6 p7 : Prop)
theorem file29_103481 : (((((p4 → False) → False) → ((p6 → p6) → (p1 → p7))) → (((p2 → p6) → False) ∧ ((p4 ∧ p1) → False))) → ((((p4 → False) ∧ (p7 → p5)) ∨ ((p2 → p3) → (p1 ∧ p0))) → (((p1 ∨ p6) → False) → ((False → True) ∨ (p5 → p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply Or.inl
      intro assump_16
      apply True.intro
  case inr assump_7 =>
    apply Or.inl
    intro assump_21
    apply True.intro


variable (p4 p3 p7 p5 p1 p0 : Prop)
theorem file29_104053 : (((((p4 ∧ p4) → (p4 ∧ True)) → False) ∧ (((p4 ∨ p5) ∨ (False ∧ p3)) → ((p0 ∧ p7) ∨ (p1 → p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : ((p4 ∧ p4) → (p4 ∧ True)) := by
      intro assump_10
      apply And.intro
      cases assump_10
      case intro assump_11 assump_12 =>
        exact assump_12
      apply True.intro
    let assump_9 := assump_2 assump_20
    apply False.elim assump_9


variable (p3 p2 p5 p0 p1 p4 p7 : Prop)
theorem file29_104570 : (((((p1 → False) ∧ (p0 ∧ p5)) ∨ ((p2 ∧ True) ∨ (p0 → False))) ∨ (((p3 ∨ True) ∧ (False ∧ True)) → False)) → ((((p4 ∨ p3) ∨ (True ∨ p7)) → False) → False)) := by
  intro assump_25
  intro assump_26
  cases assump_25
  case inl assump_29 =>
    cases assump_29
    case inl assump_31 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        cases assump_34
        case intro assump_37 assump_38 =>
          have assump_77 : ((p4 ∨ p3) ∨ (True ∨ p7)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_46 := assump_26 assump_77
          apply False.elim assump_46
    case inr assump_32 =>
      cases assump_32
      case inl assump_50 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          have assump_78 : ((p4 ∨ p3) ∨ (True ∨ p7)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_59 := assump_26 assump_78
          apply False.elim assump_59
      case inr assump_51 =>
        have assump_79 : ((p4 ∨ p3) ∨ (True ∨ p7)) := by
          apply Or.inr
          apply Or.inl
          apply True.intro
        let assump_66 := assump_26 assump_79
        apply False.elim assump_66
  case inr assump_30 =>
    have assump_80 : ((p4 ∨ p3) ∨ (True ∨ p7)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_73 := assump_26 assump_80
    apply False.elim assump_73


variable (p2 p4 p5 p1 : Prop)
theorem file29_106071 : ((((((False ∧ p1) ∨ (p2 → False)) ∧ ((p5 → False) ∧ (p4 ∧ p5))) → False) → False) → False) := by
  intro assump_1
  have assump_35 : ((((False ∧ p1) ∨ (p2 → False)) ∧ ((p5 → False) ∧ (p4 ∧ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
      case inr assump_9 =>
        cases assump_7
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            have assump_36 : p5 := by
              exact assump_21
            let assump_28 := assump_16 assump_36
            apply False.elim assump_28
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p6 p1 p7 p0 p2 p4 p3 : Prop)
theorem file29_106951 : (((((False → False) → False) → False) → False) → ((((p4 ∧ False) ∧ (p7 ∧ p2)) ∨ ((p2 ∨ p1) → False)) → (((p6 → p3) ∧ (p0 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
    case inr assump_11 =>
      have assump_38 : (((False → False) → False) → False) := by
        intro assump_25
        have assump_39 : (False → False) := by
          intro assump_29
          apply False.elim assump_29
        let assump_28 := assump_25 assump_39
        apply False.elim assump_28
      let assump_24 := assump_1 assump_38
      apply False.elim assump_24


variable (p7 p4 p6 p0 p2 p1 p5 : Prop)
theorem file29_107854 : ((((((False → False) → False) → ((p0 ∧ True) → False)) ∧ (((p7 → p0) ∧ (p4 → False)) ∧ ((p4 → True) → False))) ∧ ((((p6 → p1) ∧ (False ∨ True)) ∧ ((p5 ∨ p5) ∧ (p6 → True))) ∨ (((p6 ∧ p2) ∧ (True → False)) → False))) → False) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          cases assump_15
          case inl assump_30 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                cases assump_35
                case inl assump_38 =>
                  apply False.elim assump_38
                case inr assump_39 =>
                  cases assump_33
                  case intro assump_44 assump_45 =>
                    cases assump_44
                    case inl assump_46 =>
                      have assump_80 : (p4 → True) := by
                        intro assump_56
                        apply True.intro
                      let assump_55 := assump_21 assump_80
                      apply False.elim assump_55
                    case inr assump_47 =>
                      have assump_81 : (p4 → True) := by
                        intro assump_68
                        apply True.intro
                      let assump_67 := assump_21 assump_81
                      apply False.elim assump_67
          case inr assump_31 =>
            have assump_82 : (p4 → True) := by
              intro assump_76
              apply True.intro
            let assump_75 := assump_21 assump_82
            apply False.elim assump_75


variable (p6 p5 p0 p3 p7 p2 p4 : Prop)
theorem file29_109695 : ((((((False ∨ p6) ∧ (True ∧ p0)) → False) → False) ∧ ((((p5 ∨ p5) → False) ∧ ((p7 ∧ True) → False)) ∧ (((p2 ∨ p0) → False) ∧ ((p3 → p7) ∨ (p4 ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_15
          case inl assump_18 =>
            have assump_118 : (((False ∨ p6) ∧ (True ∧ p0)) → False) := by
              intro assump_27
              cases assump_27
              case intro assump_28 assump_29 =>
                cases assump_28
                case inl assump_30 =>
                  apply False.elim assump_30
                case inr assump_31 =>
                  cases assump_29
                  case intro assump_36 assump_37 =>
                    have assump_119 : (p2 ∨ p0) := by
                      apply Or.inr
                      exact assump_37
                    let assump_45 := assump_14 assump_119
                    apply False.elim assump_45
            let assump_26 := assump_2 assump_118
            apply False.elim assump_26
          case inr assump_19 =>
            cases assump_19
            case inl assump_52 =>
              have assump_120 : (((False ∨ p6) ∧ (True ∧ p0)) → False) := by
                intro assump_61
                cases assump_61
                case intro assump_62 assump_63 =>
                  cases assump_62
                  case inl assump_64 =>
                    apply False.elim assump_64
                  case inr assump_65 =>
                    cases assump_63
                    case intro assump_70 assump_71 =>
                      have assump_121 : (p2 ∨ p0) := by
                        apply Or.inr
                        exact assump_71
                      let assump_79 := assump_14 assump_121
                      apply False.elim assump_79
              let assump_60 := assump_2 assump_120
              apply False.elim assump_60
            case inr assump_53 =>
              have assump_122 : (((False ∨ p6) ∧ (True ∧ p0)) → False) := by
                intro assump_93
                cases assump_93
                case intro assump_94 assump_95 =>
                  cases assump_94
                  case inl assump_96 =>
                    apply False.elim assump_96
                  case inr assump_97 =>
                    cases assump_95
                    case intro assump_102 assump_103 =>
                      have assump_123 : (p2 ∨ p0) := by
                        apply Or.inr
                        exact assump_103
                      let assump_111 := assump_14 assump_123
                      apply False.elim assump_111
              let assump_92 := assump_2 assump_122
              apply False.elim assump_92


variable (p5 p6 p0 p1 p3 p4 : Prop)
theorem file29_112654 : (((((p6 ∨ p3) ∧ (p4 ∧ p5)) → False) → (((False ∨ p3) → (p0 ∨ p4)) → False)) → ((((p6 → False) → False) ∧ ((p4 ∧ p5) → (False → True))) → (((p0 ∧ p4) ∧ (False ∧ p1)) → ((p5 ∧ True) → (p0 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_12
        case intro assump_19 assump_20 =>
          apply False.elim assump_19


variable (p7 p1 p6 p4 : Prop)
theorem file29_113251 : (((((p6 ∧ False) ∧ (p1 → p7)) ∧ ((p7 ∨ p4) → False)) ∧ (((p4 ∨ p7) → (True → False)) ∨ ((p7 → False) → (p7 ∨ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9


variable (p2 p7 p4 p5 p3 p6 p1 p0 : Prop)
theorem file29_113729 : (((((p3 → p0) → False) → ((False → p7) → False)) → (((p5 → False) → False) → ((p2 → False) ∧ (p5 ∧ p3)))) → ((((True ∨ p0) → False) → ((p2 ∧ p6) ∧ (p6 → p4))) → (((p2 → True) → (False → p2)) ∨ ((p1 ∧ p6) → (p5 → p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  apply False.elim assump_8


variable (p6 p7 p1 p3 p0 p5 p2 : Prop)
theorem file29_114129 : ((((((p5 ∨ p3) ∧ (False ∨ p7)) ∧ ((p6 → p5) → (p1 → p3))) → (((p0 → p0) ∧ (p1 ∧ p6)) ∨ ((False ∧ p6) → (False ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_51 : ((((p5 ∨ p3) ∧ (False ∨ p7)) ∧ ((p6 → p5) → (p1 → p3))) → (((p0 → p0) ∧ (p1 ∧ p6)) ∨ ((False ∧ p6) → (False ∨ p2)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            apply False.elim assump_14
          case inr assump_15 =>
            apply Or.inr
            intro assump_25
            cases assump_25
            case intro assump_26 assump_27 =>
              apply False.elim assump_26
        case inr assump_11 =>
          cases assump_9
          case inl assump_32 =>
            apply False.elim assump_32
          case inr assump_33 =>
            apply Or.inr
            intro assump_43
            cases assump_43
            case intro assump_44 assump_45 =>
              apply False.elim assump_44
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p5 p6 p2 p3 p0 p4 : Prop)
theorem file29_115364 : ((((((p3 → False) → (p5 ∨ True)) ∧ ((p3 → p2) ∨ (p6 ∧ False))) → (((True → False) → False) → ((p0 ∧ False) → (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p3 → False) → (p5 ∨ True)) ∧ ((p3 → p2) ∨ (p6 ∧ False))) → (((True → False) → False) → ((p0 ∧ False) → (p4 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p3 p0 p2 : Prop)
theorem file29_115960 : (((((False → False) ∨ (p3 → p0)) ∨ ((p2 ∨ p2) ∨ (False ∨ True))) ∧ (((True → False) ∨ (p3 ∧ p2)) ∧ ((False → False) → (p2 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            have assump_189 : True := by
              apply True.intro
            let assump_23 := assump_12 assump_189
            apply False.elim assump_23
          case inr assump_13 =>
            cases assump_13
            case intro assump_27 assump_28 =>
              have assump_190 : (False → False) := by
                intro assump_36
                apply False.elim assump_36
              let assump_35 := assump_11 assump_190
              have assump_191 : p2 := by
                exact assump_28
              let assump_39 := assump_35 assump_191
              apply False.elim assump_39
      case inr assump_7 =>
        cases assump_3
        case intro assump_45 assump_46 =>
          cases assump_45
          case inl assump_47 =>
            have assump_192 : True := by
              apply True.intro
            let assump_58 := assump_47 assump_192
            apply False.elim assump_58
          case inr assump_48 =>
            cases assump_48
            case intro assump_62 assump_63 =>
              have assump_193 : (False → False) := by
                intro assump_71
                apply False.elim assump_71
              let assump_70 := assump_46 assump_193
              have assump_194 : p2 := by
                exact assump_63
              let assump_74 := assump_70 assump_194
              apply False.elim assump_74
    case inr assump_5 =>
      cases assump_5
      case inl assump_78 =>
        cases assump_78
        case inl assump_80 =>
          cases assump_3
          case intro assump_84 assump_85 =>
            cases assump_84
            case inl assump_86 =>
              have assump_195 : (False → False) := by
                intro assump_93
                apply False.elim assump_93
              let assump_92 := assump_85 assump_195
              have assump_196 : p2 := by
                exact assump_80
              let assump_96 := assump_92 assump_196
              apply False.elim assump_96
            case inr assump_87 =>
              cases assump_87
              case intro assump_100 assump_101 =>
                have assump_197 : (False → False) := by
                  intro assump_109
                  apply False.elim assump_109
                let assump_108 := assump_85 assump_197
                have assump_198 : p2 := by
                  exact assump_101
                let assump_112 := assump_108 assump_198
                apply False.elim assump_112
        case inr assump_81 =>
          cases assump_3
          case intro assump_118 assump_119 =>
            cases assump_118
            case inl assump_120 =>
              have assump_199 : (False → False) := by
                intro assump_127
                apply False.elim assump_127
              let assump_126 := assump_119 assump_199
              have assump_200 : p2 := by
                exact assump_81
              let assump_130 := assump_126 assump_200
              apply False.elim assump_130
            case inr assump_121 =>
              cases assump_121
              case intro assump_134 assump_135 =>
                have assump_201 : (False → False) := by
                  intro assump_143
                  apply False.elim assump_143
                let assump_142 := assump_119 assump_201
                have assump_202 : p2 := by
                  exact assump_135
                let assump_146 := assump_142 assump_202
                apply False.elim assump_146
      case inr assump_79 =>
        cases assump_79
        case inl assump_150 =>
          apply False.elim assump_150
        case inr assump_151 =>
          cases assump_3
          case intro assump_156 assump_157 =>
            cases assump_156
            case inl assump_158 =>
              have assump_203 : True := by
                apply True.intro
              let assump_169 := assump_158 assump_203
              apply False.elim assump_169
            case inr assump_159 =>
              cases assump_159
              case intro assump_173 assump_174 =>
                have assump_204 : (False → False) := by
                  intro assump_182
                  apply False.elim assump_182
                let assump_181 := assump_157 assump_204
                have assump_205 : p2 := by
                  exact assump_174
                let assump_185 := assump_181 assump_205
                apply False.elim assump_185


variable (p1 p0 p7 p6 p2 p5 : Prop)
theorem file29_120872 : ((((((p5 → False) ∧ (p0 ∧ p2)) → ((p5 ∨ p1) → (p2 ∨ p2))) → (((p7 → False) ∨ (p0 ∧ p6)) → ((p1 ∨ p5) → (p6 → p6)))) → False) → False) := by
  intro assump_1
  have assump_48 : ((((p5 → False) ∧ (p0 ∧ p2)) → ((p5 ∨ p1) → (p2 ∨ p2))) → (((p7 → False) ∨ (p0 ∧ p6)) → ((p1 ∨ p5) → (p6 → p6)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case inl assump_11 =>
      cases assump_6
      case inl assump_15 =>
        exact assump_8
      case inr assump_16 =>
        cases assump_16
        case intro assump_21 assump_22 =>
          exact assump_22
    case inr assump_12 =>
      cases assump_6
      case inl assump_31 =>
        exact assump_8
      case inr assump_32 =>
        cases assump_32
        case intro assump_37 assump_38 =>
          exact assump_38
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p7 p6 p1 p0 p4 p3 p2 p5 : Prop)
theorem file29_121830 : ((((((p7 ∧ p1) → (p3 → p7)) ∨ ((p5 ∨ False) → (p6 ∧ p7))) ∨ (((p5 ∧ p7) ∧ (p2 → p0)) ∧ ((p0 → False) ∨ (p2 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p7 ∧ p1) → (p3 → p7)) ∨ ((p5 ∨ False) → (p6 ∧ p7))) ∨ (((p5 ∧ p7) ∧ (p2 → p0)) ∧ ((p0 → False) ∨ (p2 ∨ p4)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_9
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


