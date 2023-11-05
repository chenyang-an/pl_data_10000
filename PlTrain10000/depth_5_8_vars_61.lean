variable (p4 p0 p3 p1 p6 : Prop)
theorem file61_41 : (((((p1 ∨ p6) → False) → ((p6 ∨ p3) ∨ (p0 → False))) → False) → ((((p0 ∨ p0) → False) → False) ∨ (((p4 ∧ True) → (p4 ∧ p1)) ∧ ((p3 → False) ∨ (p0 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_24 : (((p1 ∨ p6) → False) → ((p6 ∨ p3) ∨ (p0 → False))) := by
    intro assump_9
    apply Or.inr
    intro assump_12
    have assump_25 : (p0 ∨ p0) := by
      apply Or.inl
      exact assump_12
    let assump_17 := assump_4 assump_25
    apply False.elim assump_17
  let assump_8 := assump_1 assump_24
  apply False.elim assump_8


variable (p5 p7 p2 p0 p4 p3 p6 p1 : Prop)
theorem file61_667 : ((((((p7 ∧ p6) → False) ∨ ((False ∨ p4) ∧ (p0 ∨ p0))) → (((p5 ∧ p0) ∧ (p7 ∨ p7)) ∨ ((p1 → p6) ∧ (p6 → False)))) ∧ ((((False ∨ p6) → False) → ((p2 → p1) → (p3 → True))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_19 : (((False ∨ p6) → False) → ((p2 → p1) → (p3 → True))) := by
      intro assump_13
      intro assump_14
      intro assump_15
      apply True.intro
    let assump_12 := assump_7 assump_19
    apply False.elim assump_12


variable (p2 p3 p0 p7 p1 : Prop)
theorem file61_1225 : (((((p3 ∨ p1) ∧ (False → False)) ∧ ((p7 ∧ p1) → (p2 → False))) ∧ (((True → False) → (False → p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          have assump_42 : ((True → False) → (False → p0)) := by
            intro assump_19
            intro assump_20
            apply False.elim assump_20
          let assump_18 := assump_3 assump_42
          apply False.elim assump_18
        case inr assump_9 =>
          have assump_43 : ((True → False) → (False → p0)) := by
            intro assump_35
            intro assump_36
            apply False.elim assump_36
          let assump_34 := assump_3 assump_43
          apply False.elim assump_34


variable (p5 p0 p1 p7 p2 p6 : Prop)
theorem file61_2157 : (((((False ∨ True) ∨ (p2 → False)) → False) ∧ (((p1 ∧ p7) ∧ (p7 ∨ p5)) → False)) → ((((False ∧ p0) ∧ (p1 ∨ p6)) ∨ ((p2 ∧ p0) ∨ (p0 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7
  case inr assump_4 =>
    cases assump_4
    case inl assump_11 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_1
        case intro assump_19 assump_20 =>
          have assump_43 : ((False ∨ True) ∨ (p2 → False)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_26 := assump_19 assump_43
          apply False.elim assump_26
    case inr assump_12 =>
      cases assump_1
      case intro assump_32 assump_33 =>
        have assump_44 : ((False ∨ True) ∨ (p2 → False)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_39 := assump_32 assump_44
        apply False.elim assump_39


variable (p4 p0 p3 p2 p6 p1 p7 : Prop)
theorem file61_3326 : (((((p0 ∧ p3) → (p7 ∨ p1)) ∧ ((p0 → False) ∨ (p3 ∧ p3))) → False) → ((((p0 ∨ True) ∨ (p2 → p6)) → False) → (((False ∨ p1) → False) → ((p4 ∧ p3) → (p0 → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply True.intro


variable (p0 p2 p7 p5 p1 p4 p6 : Prop)
theorem file61_3661 : (((((False → False) ∧ (p1 → True)) → False) → (((p6 ∧ p0) → False) ∨ ((p6 ∨ True) ∧ (True → p0)))) ∨ ((((p0 → p4) ∧ (p1 → True)) → ((p2 ∨ p5) → False)) ∧ (((True ∧ True) → (True → False)) ∨ ((p5 ∨ False) ∨ (p7 ∧ p1))))) := by
  apply Or.inl
  intro assump_5
  apply Or.inl
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    have assump_25 : ((False → False) ∧ (p1 → True)) := by
      apply And.intro
      intro assump_18
      apply False.elim assump_18
      intro assump_21
      apply True.intro
    let assump_17 := assump_5 assump_25
    apply False.elim assump_17


variable (p5 p7 p2 p4 p0 : Prop)
theorem file61_4312 : (((((True ∨ p2) → (p2 → p0)) → False) → (((p7 ∧ False) → False) ∨ ((p2 ∧ p5) ∨ (p4 → p0)))) ∨ ((((p2 ∨ p0) ∨ (p7 → False)) → ((p0 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p7 p2 p6 p1 : Prop)
theorem file61_4676 : (((((True → False) → False) → False) ∧ (((p6 ∧ p2) ∧ (p2 ∨ p7)) → ((p1 ∨ p2) ∨ (True ∧ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : ((True → False) → False) := by
      intro assump_10
      have assump_21 : True := by
        apply True.intro
      let assump_13 := assump_10 assump_21
      apply False.elim assump_13
    let assump_9 := assump_2 assump_20
    apply False.elim assump_9


variable (p6 p0 p2 : Prop)
theorem file61_5182 : ((((((p2 ∧ False) ∧ (True ∨ p2)) ∧ ((p6 → p0) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p2 ∧ False) ∧ (True ∨ p2)) ∧ ((p6 → p0) → False)) → False) := by
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


variable (p6 p2 p4 p0 : Prop)
theorem file61_5730 : ((((((p0 ∧ p6) ∨ (p6 → p2)) ∧ ((p4 ∨ True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p0 ∧ p6) ∨ (p6 → p2)) ∧ ((p4 ∨ True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_34 : (p4 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_18 := assump_7 assump_34
          apply False.elim assump_18
      case inr assump_9 =>
        have assump_35 : (p4 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_26 := assump_7 assump_35
        apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p0 p4 p2 p5 p6 p3 : Prop)
theorem file61_6611 : (((((p5 ∧ p5) ∧ (False ∧ p4)) ∨ ((p2 ∧ p5) ∧ (False ∧ p3))) → (((p4 → p4) → False) ∨ ((True ∧ p0) ∧ (p6 ∧ p6)))) ∨ ((((True ∧ p6) ∨ (p6 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  case inr assump_3 =>
    cases assump_3
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_17
        case intro assump_24 assump_25 =>
          apply False.elim assump_24


variable (p4 p2 p1 p6 p7 : Prop)
theorem file61_7372 : (((((p2 → False) ∨ (True ∧ p1)) → ((p1 ∧ p4) ∧ (False ∧ p4))) ∧ (((False → False) ∨ (True → p4)) ∧ ((p2 → False) ∧ (p6 ∨ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            have assump_120 : ((p2 → False) ∨ (True ∧ p1)) := by
              apply Or.inl
              intro assump_24
              have assump_121 : p2 := by
                exact assump_24
              let assump_29 := assump_12 assump_121
              apply False.elim assump_29
            let assump_23 := assump_2 assump_120
            let assump_33 := And.right assump_23
            let assump_37 := And.left assump_33
            apply False.elim assump_37
          case inr assump_17 =>
            have assump_122 : ((p2 → False) ∨ (True ∧ p1)) := by
              apply Or.inl
              intro assump_47
              have assump_123 : p2 := by
                exact assump_47
              let assump_52 := assump_12 assump_123
              apply False.elim assump_52
            let assump_46 := assump_2 assump_122
            let assump_56 := And.right assump_46
            let assump_60 := And.left assump_56
            apply False.elim assump_60
      case inr assump_9 =>
        cases assump_7
        case intro assump_66 assump_67 =>
          cases assump_67
          case inl assump_70 =>
            have assump_124 : ((p2 → False) ∨ (True ∧ p1)) := by
              apply Or.inl
              intro assump_79
              have assump_125 : p2 := by
                exact assump_79
              let assump_84 := assump_66 assump_125
              apply False.elim assump_84
            let assump_78 := assump_2 assump_124
            let assump_88 := And.right assump_78
            let assump_92 := And.left assump_88
            apply False.elim assump_92
          case inr assump_71 =>
            have assump_126 : ((p2 → False) ∨ (True ∧ p1)) := by
              apply Or.inl
              intro assump_103
              have assump_127 : p2 := by
                exact assump_103
              let assump_108 := assump_66 assump_127
              apply False.elim assump_108
            let assump_102 := assump_2 assump_126
            let assump_112 := And.right assump_102
            let assump_116 := And.left assump_112
            apply False.elim assump_116


variable (p0 p2 p6 p7 p4 p5 p3 p1 : Prop)
theorem file61_9991 : ((((((p6 → p4) → False) ∧ ((True → p3) ∧ (False → p4))) → False) ∧ ((((p4 ∨ p1) → False) ∨ ((p1 ∧ p2) ∨ (True ∨ p7))) ∧ (((p6 → True) → False) ∧ ((p5 ∧ True) → (p1 ∨ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          have assump_74 : (p6 → True) := by
            intro assump_20
            apply True.intro
          let assump_19 := assump_12 assump_74
          apply False.elim assump_19
      case inr assump_9 =>
        cases assump_9
        case inl assump_24 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            cases assump_7
            case intro assump_32 assump_33 =>
              have assump_75 : (p6 → True) := by
                intro assump_40
                apply True.intro
              let assump_39 := assump_32 assump_75
              apply False.elim assump_39
        case inr assump_25 =>
          cases assump_25
          case inl assump_44 =>
            cases assump_7
            case intro assump_48 assump_49 =>
              have assump_76 : (p6 → True) := by
                intro assump_56
                apply True.intro
              let assump_55 := assump_48 assump_76
              apply False.elim assump_55
          case inr assump_45 =>
            cases assump_7
            case intro assump_62 assump_63 =>
              have assump_77 : (p6 → True) := by
                intro assump_70
                apply True.intro
              let assump_69 := assump_62 assump_77
              apply False.elim assump_69


variable (p0 p3 p6 p1 p7 p4 : Prop)
theorem file61_11769 : (((((p3 ∧ p4) ∨ (True ∨ True)) ∨ ((p1 ∧ p7) → (p1 → False))) → False) → ((((False ∧ True) ∧ (False → False)) ∨ ((p0 ∨ False) → (True ∨ False))) → (((p1 ∨ p6) ∨ (p6 ∧ True)) → ((False ∧ True) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p2 p4 p5 p1 p3 p6 : Prop)
theorem file61_12187 : (((((p2 ∨ p6) ∨ (True ∨ p2)) ∨ ((False → p3) → False)) → False) → ((((p4 ∧ p1) → (p2 ∧ p3)) ∧ ((p2 ∨ p6) ∨ (p4 → False))) ∧ (((p6 → p5) ∧ (p1 → False)) → False))) := by
  intro assump_62
  apply And.intro
  apply And.intro
  intro assump_63
  apply And.intro
  cases assump_63
  case intro assump_64 assump_65 =>
    have assump_111 : (((p2 ∨ p6) ∨ (True ∨ p2)) ∨ ((False → p3) → False)) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_72 := assump_62 assump_111
    apply False.elim assump_72
  cases assump_63
  case intro assump_76 assump_77 =>
    have assump_112 : (((p2 ∨ p6) ∨ (True ∨ p2)) ∨ ((False → p3) → False)) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_84 := assump_62 assump_112
    apply False.elim assump_84
  apply Or.inr
  intro assump_90
  have assump_113 : (((p2 ∨ p6) ∨ (True ∨ p2)) ∨ ((False → p3) → False)) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_94 := assump_62 assump_113
  apply False.elim assump_94
  intro assump_98
  cases assump_98
  case intro assump_99 assump_100 =>
    have assump_114 : (((p2 ∨ p6) ∨ (True ∨ p2)) ∨ ((False → p3) → False)) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_107 := assump_62 assump_114
    apply False.elim assump_107


variable (p1 p5 p4 p3 p0 p6 p2 p7 : Prop)
theorem file61_13650 : (((((p2 ∨ p7) ∨ (p7 ∧ p4)) ∨ ((p7 → p0) ∨ (p0 → p5))) → (((p6 ∨ p7) → False) → ((p7 ∧ p1) ∧ (p6 → True)))) → ((((False ∧ p6) ∧ (p3 ∧ p4)) → ((p3 ∨ False) ∧ (p0 → False))) ∨ (((True → False) → False) ∨ ((True → False) ∨ (True ∧ p6))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  intro assump_11
  cases assump_4
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      apply False.elim assump_16


variable (p3 p5 p4 p2 p6 p1 p7 : Prop)
theorem file61_14321 : ((((((p1 → p2) → False) ∨ ((p4 → p2) ∧ (p3 ∨ False))) ∧ (((True ∧ p7) ∧ (p1 ∧ True)) ∧ ((p7 → p4) ∧ (False ∧ True)))) ∧ ((((p3 ∧ p5) → False) → False) → (((False → False) ∨ (p7 → False)) → ((p6 → False) ∨ (True → False))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                cases assump_15
                case intro assump_30 assump_31 =>
                  cases assump_31
                  case intro assump_34 assump_35 =>
                    apply False.elim assump_34
      case inr assump_11 =>
        cases assump_11
        case intro assump_38 assump_39 =>
          cases assump_39
          case inl assump_42 =>
            cases assump_9
            case intro assump_46 assump_47 =>
              cases assump_46
              case intro assump_48 assump_49 =>
                cases assump_48
                case intro assump_50 assump_51 =>
                  cases assump_49
                  case intro assump_56 assump_57 =>
                    cases assump_47
                    case intro assump_62 assump_63 =>
                      cases assump_63
                      case intro assump_66 assump_67 =>
                        apply False.elim assump_66
          case inr assump_43 =>
            apply False.elim assump_43


variable (p4 p0 p6 : Prop)
theorem file61_16062 : (((((p0 ∧ p4) → (True ∨ False)) ∨ ((True → False) ∨ (p6 ∧ p4))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p0 ∧ p4) → (True ∨ False)) ∨ ((True → False) ∨ (p6 ∧ p4))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p1 p0 p5 p6 p4 : Prop)
theorem file61_16512 : ((((((p5 ∧ True) → False) ∨ ((p5 ∧ p6) → (p3 ∧ p0))) ∧ (((p0 ∧ p1) → (p4 ∧ p4)) → False)) ∧ ((((p4 → True) ∨ (p1 ∨ p6)) ∨ ((p6 → p4) → (p5 → False))) → False)) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        have assump_40 : (((p4 → True) ∨ (p1 ∨ p6)) ∨ ((p6 → p4) → (p5 → False))) := by
          apply Or.inl
          apply Or.inl
          intro assump_25
          apply True.intro
        let assump_24 := assump_13 assump_40
        apply False.elim assump_24
      case inr assump_17 =>
        have assump_41 : (((p4 → True) ∨ (p1 ∨ p6)) ∨ ((p6 → p4) → (p5 → False))) := by
          apply Or.inl
          apply Or.inl
          intro assump_36
          apply True.intro
        let assump_35 := assump_13 assump_41
        apply False.elim assump_35


variable (p5 p2 p3 p1 p7 p4 : Prop)
theorem file61_17489 : (((((True ∨ p1) → False) ∧ ((p7 ∨ p5) ∧ (p5 ∨ p7))) ∧ (((p7 → p3) ∧ (True ∧ p2)) ∧ ((p4 ∧ p1) → (p1 → p7)))) → False) := by
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
          case inl assump_14 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  have assump_123 : (True ∨ p1) := by
                    apply Or.inl
                    apply True.intro
                  let assump_38 := assump_4 assump_123
                  apply False.elim assump_38
          case inr assump_15 =>
            cases assump_3
            case intro assump_44 assump_45 =>
              cases assump_44
              case intro assump_46 assump_47 =>
                cases assump_47
                case intro assump_50 assump_51 =>
                  have assump_124 : (True ∨ p1) := by
                    apply Or.inl
                    apply True.intro
                  let assump_64 := assump_4 assump_124
                  apply False.elim assump_64
        case inr assump_11 =>
          cases assump_9
          case inl assump_70 =>
            cases assump_3
            case intro assump_74 assump_75 =>
              cases assump_74
              case intro assump_76 assump_77 =>
                cases assump_77
                case intro assump_80 assump_81 =>
                  have assump_125 : (True ∨ p1) := by
                    apply Or.inl
                    apply True.intro
                  let assump_93 := assump_4 assump_125
                  apply False.elim assump_93
          case inr assump_71 =>
            cases assump_3
            case intro assump_99 assump_100 =>
              cases assump_99
              case intro assump_101 assump_102 =>
                cases assump_102
                case intro assump_105 assump_106 =>
                  have assump_126 : (True ∨ p1) := by
                    apply Or.inl
                    apply True.intro
                  let assump_119 := assump_4 assump_126
                  apply False.elim assump_119


variable (p6 p0 p5 p1 p7 p3 : Prop)
theorem file61_19952 : (((((False ∧ p3) ∧ (p1 ∧ True)) ∧ ((False ∨ p1) → False)) → False) ∧ ((((p7 → False) ∧ (True → False)) → ((p6 → p6) → False)) ∨ (((p5 ∧ True) → (p0 ∧ p3)) → ((p1 → p7) ∧ (p1 → False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6
  apply Or.inl
  intro assump_10
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    have assump_24 : True := by
      apply True.intro
    let assump_20 := assump_15 assump_24
    apply False.elim assump_20


variable (p5 p3 p6 p4 p7 : Prop)
theorem file61_20668 : ((((((True → False) ∨ (p6 ∨ p3)) ∧ ((p7 ∨ p4) → (p5 ∧ True))) → (((p5 ∨ p7) ∧ (p4 ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_30 : ((((True → False) ∨ (p6 ∨ p3)) ∧ ((p7 ∨ p4) → (p5 ∧ True))) → (((p5 ∨ p7) ∧ (p4 ∧ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
      case inr assump_10 =>
        cases assump_8
        case intro assump_21 assump_22 =>
          apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p1 p3 p0 p6 p7 p4 : Prop)
theorem file61_21437 : (((((p3 ∧ p3) → False) ∨ ((False → False) → (p4 → p1))) → False) → ((((p2 → False) → (True → False)) ∧ ((p2 → False) ∨ (p0 → p7))) → (((False → True) ∨ (p6 → False)) ∧ ((False → False) ∧ (True ∨ p1))))) := by
  intro assump_22
  intro assump_23
  apply And.intro
  cases assump_23
  case intro assump_24 assump_25 =>
    cases assump_25
    case inl assump_28 =>
      apply Or.inl
      intro assump_34
      apply True.intro
    case inr assump_29 =>
      apply Or.inl
      intro assump_39
      apply True.intro
  apply And.intro
  intro assump_40
  apply False.elim assump_40
  cases assump_23
  case intro assump_43 assump_44 =>
    cases assump_44
    case inl assump_47 =>
      apply Or.inl
      apply True.intro
    case inr assump_48 =>
      apply Or.inl
      apply True.intro


variable (p7 p4 p6 p2 p3 p1 p5 p0 : Prop)
theorem file61_22295 : ((((((p5 → p7) ∨ (False → p2)) ∧ ((p7 → p3) ∨ (p7 → False))) ∨ (((p5 → p0) ∨ (p6 → True)) → False)) ∧ ((((p0 ∧ p4) ∨ (p1 ∨ p3)) → ((False → False) ∧ (False → p6))) → False)) → False) := by
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
            have assump_93 : (((p0 ∧ p4) ∨ (p1 ∨ p3)) → ((False → False) ∧ (False → p6))) := by
              intro assump_19
              apply And.intro
              intro assump_20
              apply False.elim assump_20
              intro assump_23
              apply False.elim assump_23
            let assump_18 := assump_3 assump_93
            apply False.elim assump_18
          case inr assump_13 =>
            have assump_94 : (((p0 ∧ p4) ∨ (p1 ∨ p3)) → ((False → False) ∧ (False → p6))) := by
              intro assump_34
              apply And.intro
              intro assump_35
              apply False.elim assump_35
              intro assump_38
              apply False.elim assump_38
            let assump_33 := assump_3 assump_94
            apply False.elim assump_33
        case inr assump_9 =>
          cases assump_7
          case inl assump_46 =>
            have assump_95 : (((p0 ∧ p4) ∨ (p1 ∨ p3)) → ((False → False) ∧ (False → p6))) := by
              intro assump_53
              apply And.intro
              intro assump_54
              apply False.elim assump_54
              intro assump_57
              apply False.elim assump_57
            let assump_52 := assump_3 assump_95
            apply False.elim assump_52
          case inr assump_47 =>
            have assump_96 : (((p0 ∧ p4) ∨ (p1 ∨ p3)) → ((False → False) ∧ (False → p6))) := by
              intro assump_68
              apply And.intro
              intro assump_69
              apply False.elim assump_69
              intro assump_72
              apply False.elim assump_72
            let assump_67 := assump_3 assump_96
            apply False.elim assump_67
    case inr assump_5 =>
      have assump_97 : (((p0 ∧ p4) ∨ (p1 ∨ p3)) → ((False → False) ∧ (False → p6))) := by
        intro assump_83
        apply And.intro
        intro assump_84
        apply False.elim assump_84
        intro assump_87
        apply False.elim assump_87
      let assump_82 := assump_3 assump_97
      apply False.elim assump_82


variable (p7 p4 p5 p0 p1 : Prop)
theorem file61_24867 : ((((((p5 → p4) ∨ (p0 → False)) → False) → (((True → False) → False) ∨ ((p7 ∧ p1) → (p4 → True)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 → p4) ∨ (p0 → False)) → False) → (((True → False) → False) ∨ ((p7 ∧ p1) → (p4 → True)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p2 : Prop)
theorem file61_25421 : ((((((True → False) → (p5 → p2)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → False) → (p5 → p2)) → False) → False) := by
    intro assump_5
    have assump_26 : ((True → False) → (p5 → p2)) := by
      intro assump_9
      intro assump_10
      have assump_27 : True := by
        apply True.intro
      let assump_15 := assump_9 assump_27
      apply False.elim assump_15
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p7 p1 p5 p3 p6 p4 : Prop)
theorem file61_26036 : (((((p6 → p5) → (p1 ∨ p7)) → ((p6 → p1) ∧ (p0 → False))) ∧ (((p7 ∧ p1) → (p6 ∧ p4)) → False)) → ((((p3 ∧ p4) → False) → ((p3 → False) → False)) → (((p5 ∧ p7) ∧ (True → p5)) ∨ ((False ∨ False) → (p0 → p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inr
    intro assump_11
    intro assump_12
    cases assump_11
    case inl assump_15 =>
      apply False.elim assump_15
    case inr assump_16 =>
      apply False.elim assump_16


variable (p2 p0 p5 p1 p6 p4 p7 p3 : Prop)
theorem file61_26596 : (((((p3 → p2) ∨ (p7 ∨ p1)) → ((p1 → True) ∨ (True → False))) → (((p3 → False) → (True ∨ p3)) ∨ ((p6 ∧ p5) ∨ (p0 → p4)))) ∨ ((((p2 ∨ p2) → (True → p1)) ∨ ((p2 ∧ p2) → False)) → (((p7 → True) → (False ∨ True)) → ((True → False) ∧ (p7 ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  apply True.intro


variable (p2 p4 p6 p5 p0 : Prop)
theorem file61_26999 : ((((((p2 → False) ∧ (True ∧ p0)) → False) → (((p0 → p0) ∨ (p5 → False)) ∨ ((p5 → False) ∧ (p4 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 → False) ∧ (True ∧ p0)) → False) → (((p0 → p0) ∨ (p5 → False)) ∨ ((p5 → False) ∧ (p4 ∨ p6)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p7 p6 p0 p5 p2 p4 : Prop)
theorem file61_27488 : ((((((p6 → False) ∨ (True → p4)) ∨ ((p7 ∧ p0) → False)) → False) ∧ ((((p1 → False) ∧ (p2 ∧ p7)) ∧ ((True ∨ True) → (p0 ∧ p2))) ∧ (((p5 ∨ p5) → (p1 → p1)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            have assump_42 : ((p5 ∨ p5) → (p1 → p1)) := by
              intro assump_29
              intro assump_30
              cases assump_29
              case inl assump_33 =>
                exact assump_30
              case inr assump_34 =>
                exact assump_30
            let assump_28 := assump_11 assump_42
            apply False.elim assump_28


variable (p4 p5 p1 p0 p6 p3 p2 p7 : Prop)
theorem file61_28430 : (((((p4 ∨ p2) → (p7 ∧ p5)) → ((p2 → False) → False)) → (((p5 ∨ p6) ∨ (p1 ∨ p4)) → ((p5 ∨ p3) ∧ (p3 ∧ p3)))) → ((((p5 → False) → (p5 → False)) ∨ ((True → p5) ∨ (p7 → False))) ∨ (((p0 → False) ∧ (p7 ∧ p6)) ∧ ((p4 ∧ p7) ∧ (p5 → p7))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_14 : p5 := by
    exact assump_5
  let assump_10 := assump_4 assump_14
  apply False.elim assump_10


variable (p2 p0 p1 p7 p6 p5 : Prop)
theorem file61_28924 : (((((False → False) ∨ (p1 ∨ p6)) ∨ ((p0 → p1) → False)) ∨ (((p0 → False) → False) ∧ ((True ∧ p1) ∨ (p0 → False)))) ∨ ((((True → False) ∧ (p6 → p7)) → False) → (((p6 ∨ p2) ∧ (p5 → False)) ∧ ((p7 → True) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p2 p4 p5 p7 : Prop)
theorem file61_29303 : ((((((p5 → False) → False) → False) → False) ∧ ((((False ∧ p5) → False) ∨ ((p5 ∧ p7) ∨ (p4 ∧ p2))) → False)) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    have assump_30 : (((False ∧ p5) → False) ∨ ((p5 ∧ p7) ∨ (p4 ∧ p2))) := by
      apply Or.inl
      intro assump_22
      cases assump_22
      case intro assump_23 assump_24 =>
        apply False.elim assump_23
    let assump_21 := assump_16 assump_30
    apply False.elim assump_21


variable (p1 p5 p0 p2 p7 p6 p4 : Prop)
theorem file61_29850 : ((((((p0 → p1) → False) ∨ ((p6 → False) ∧ (p4 ∧ p7))) → (((p2 ∧ p1) → (p5 ∨ p0)) ∧ ((p7 ∨ p5) → (p6 → False)))) ∧ ((((p4 ∨ p7) → False) → False) ∧ (((p2 ∨ p0) ∨ (True ∧ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_16 : ((p2 ∨ p0) ∨ (True ∧ True)) := by
        apply Or.inr
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_12 := assump_7 assump_16
      apply False.elim assump_12


variable (p6 p4 p2 p3 p5 p1 : Prop)
theorem file61_30462 : (((((True ∨ p6) → (False ∧ p3)) → False) → (((True ∨ p4) → False) ∧ ((p5 ∨ p4) → False))) → ((((p1 ∨ True) ∨ (p2 → False)) ∧ ((p2 ∧ p5) ∧ (False ∧ True))) ∧ (((p3 → p2) → (p5 ∨ p2)) ∧ ((True → True) ∧ (p6 ∨ False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  apply Or.inr
  apply True.intro
  apply And.intro
  apply And.intro
  have assump_88 : (((True ∨ p6) → (False ∧ p3)) → False) := by
    intro assump_7
    have assump_89 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_10 := assump_7 assump_89
    let assump_11 := And.left assump_10
    apply False.elim assump_11
  let assump_6 := assump_1 assump_88
  let assump_15 := And.left assump_6
  have assump_90 : (True ∨ p4) := by
    apply Or.inl
    apply True.intro
  let assump_16 := assump_15 assump_90
  apply False.elim assump_16
  have assump_91 : (((True ∨ p6) → (False ∧ p3)) → False) := by
    intro assump_23
    have assump_92 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_26 := assump_23 assump_92
    let assump_27 := And.left assump_26
    apply False.elim assump_27
  let assump_22 := assump_1 assump_91
  let assump_31 := And.left assump_22
  have assump_93 : (True ∨ p4) := by
    apply Or.inl
    apply True.intro
  let assump_32 := assump_31 assump_93
  apply False.elim assump_32
  apply And.intro
  have assump_94 : (((True ∨ p6) → (False ∧ p3)) → False) := by
    intro assump_39
    have assump_95 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_42 := assump_39 assump_95
    let assump_43 := And.left assump_42
    apply False.elim assump_43
  let assump_38 := assump_1 assump_94
  let assump_47 := And.left assump_38
  have assump_96 : (True ∨ p4) := by
    apply Or.inl
    apply True.intro
  let assump_48 := assump_47 assump_96
  apply False.elim assump_48
  apply True.intro
  apply And.intro
  intro assump_52
  have assump_97 : (((True ∨ p6) → (False ∧ p3)) → False) := by
    intro assump_58
    have assump_98 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_61 := assump_58 assump_98
    let assump_62 := And.left assump_61
    apply False.elim assump_62
  let assump_57 := assump_1 assump_97
  let assump_66 := And.left assump_57
  have assump_99 : (True ∨ p4) := by
    apply Or.inl
    apply True.intro
  let assump_67 := assump_66 assump_99
  apply False.elim assump_67
  apply And.intro
  intro assump_71
  apply True.intro
  have assump_100 : (((True ∨ p6) → (False ∧ p3)) → False) := by
    intro assump_75
    have assump_101 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_78 := assump_75 assump_101
    let assump_79 := And.left assump_78
    apply False.elim assump_79
  let assump_74 := assump_1 assump_100
  let assump_83 := And.left assump_74
  have assump_102 : (True ∨ p4) := by
    apply Or.inl
    apply True.intro
  let assump_84 := assump_83 assump_102
  apply False.elim assump_84


variable (p5 p4 p1 p7 p3 p6 p2 : Prop)
theorem file61_33497 : (((((p2 → p6) → False) → ((p6 ∧ p6) → (p4 → False))) ∨ (((p2 → p1) → False) → ((p5 ∨ p2) ∨ (p7 → False)))) ∨ ((((p4 → p5) ∧ (p4 → False)) ∨ ((p4 → False) ∨ (p2 → p7))) ∧ (((p4 → p5) → False) ∨ ((p3 ∨ p1) → (p6 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    have assump_21 : (p2 → p6) := by
      intro assump_15
      exact assump_7
    let assump_14 := assump_1 assump_21
    apply False.elim assump_14


variable (p2 p1 p3 p5 p0 p7 p6 : Prop)
theorem file61_34072 : ((((((p7 → False) → (p3 → False)) → ((p5 → p6) ∨ (p2 → False))) ∨ (((True → True) → (p1 ∨ p5)) → False)) ∧ ((((True ∧ p5) ∧ (False ∧ p7)) ∧ ((p0 → False) → False)) ∧ (((p1 ∧ p0) → (p5 → p5)) ∧ ((p3 → False) ∧ (True ∨ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              cases assump_13
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
    case inr assump_5 =>
      cases assump_3
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              cases assump_31
              case intro assump_38 assump_39 =>
                apply False.elim assump_38


variable (p1 p7 p6 : Prop)
theorem file61_35283 : ((((((p1 ∧ p7) → (p1 ∨ p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p1 ∧ p7) → (p1 ∨ p6)) → False) → False) := by
    intro assump_5
    have assump_23 : ((p1 ∧ p7) → (p1 ∨ p6)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inl
        exact assump_10
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p5 p4 p7 p0 p3 p1 p2 : Prop)
theorem file61_35836 : ((((((p6 ∨ p3) ∨ (p1 → False)) ∧ ((False → False) ∨ (p5 ∧ p7))) ∧ (((p0 ∨ p2) ∧ (p5 → False)) → ((p5 → False) ∧ (p1 ∨ False)))) ∧ ((((p5 → False) → (False → p4)) ∨ ((p4 ∧ True) → (p6 ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_7
            case inl assump_14 =>
              have assump_120 : (((p5 → False) → (False → p4)) ∨ ((p4 ∧ True) → (p6 ∨ p1))) := by
                apply Or.inl
                intro assump_23
                intro assump_24
                apply False.elim assump_24
              let assump_22 := assump_3 assump_120
              apply False.elim assump_22
            case inr assump_15 =>
              cases assump_15
              case intro assump_30 assump_31 =>
                have assump_121 : (((p5 → False) → (False → p4)) ∨ ((p4 ∧ True) → (p6 ∨ p1))) := by
                  apply Or.inl
                  intro assump_41
                  intro assump_42
                  apply False.elim assump_42
                let assump_40 := assump_3 assump_121
                apply False.elim assump_40
          case inr assump_11 =>
            cases assump_7
            case inl assump_50 =>
              have assump_122 : (((p5 → False) → (False → p4)) ∨ ((p4 ∧ True) → (p6 ∨ p1))) := by
                apply Or.inl
                intro assump_59
                intro assump_60
                apply False.elim assump_60
              let assump_58 := assump_3 assump_122
              apply False.elim assump_58
            case inr assump_51 =>
              cases assump_51
              case intro assump_66 assump_67 =>
                have assump_123 : (((p5 → False) → (False → p4)) ∨ ((p4 ∧ True) → (p6 ∨ p1))) := by
                  apply Or.inl
                  intro assump_77
                  intro assump_78
                  apply False.elim assump_78
                let assump_76 := assump_3 assump_123
                apply False.elim assump_76
        case inr assump_9 =>
          cases assump_7
          case inl assump_86 =>
            have assump_124 : (((p5 → False) → (False → p4)) ∨ ((p4 ∧ True) → (p6 ∨ p1))) := by
              apply Or.inl
              intro assump_95
              intro assump_96
              apply False.elim assump_96
            let assump_94 := assump_3 assump_124
            apply False.elim assump_94
          case inr assump_87 =>
            cases assump_87
            case intro assump_102 assump_103 =>
              have assump_125 : (((p5 → False) → (False → p4)) ∨ ((p4 ∧ True) → (p6 ∨ p1))) := by
                apply Or.inl
                intro assump_113
                intro assump_114
                apply False.elim assump_114
              let assump_112 := assump_3 assump_125
              apply False.elim assump_112


variable (p0 p7 p6 p5 p1 p2 p4 : Prop)
theorem file61_38953 : (((((p2 → p7) ∧ (p7 → p0)) ∧ ((False → p2) → False)) ∧ (((p4 ∧ True) ∨ (p1 ∧ True)) ∧ ((True → p0) ∨ (p6 ∨ p0)))) → ((((False ∨ p6) → (True → False)) → ((p2 → False) ∨ (p2 → p6))) ∧ (((p4 ∨ p5) → (False → False)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_6
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_18
              case inl assump_27 =>
                apply Or.inl
                intro assump_31
                have assump_240 : (False → p2) := by
                  intro assump_39
                  apply False.elim assump_39
                let assump_38 := assump_8 assump_240
                apply False.elim assump_38
              case inr assump_28 =>
                cases assump_28
                case inl assump_45 =>
                  apply Or.inl
                  intro assump_49
                  have assump_241 : (False → p2) := by
                    intro assump_56
                    apply False.elim assump_56
                  let assump_55 := assump_8 assump_241
                  apply False.elim assump_55
                case inr assump_46 =>
                  apply Or.inl
                  intro assump_64
                  have assump_242 : (False → p2) := by
                    intro assump_71
                    apply False.elim assump_71
                  let assump_70 := assump_8 assump_242
                  apply False.elim assump_70
          case inr assump_20 =>
            cases assump_20
            case intro assump_77 assump_78 =>
              cases assump_18
              case inl assump_83 =>
                apply Or.inl
                intro assump_87
                have assump_243 : (False → p2) := by
                  intro assump_95
                  apply False.elim assump_95
                let assump_94 := assump_8 assump_243
                apply False.elim assump_94
              case inr assump_84 =>
                cases assump_84
                case inl assump_101 =>
                  apply Or.inl
                  intro assump_105
                  have assump_244 : (False → p2) := by
                    intro assump_112
                    apply False.elim assump_112
                  let assump_111 := assump_8 assump_244
                  apply False.elim assump_111
                case inr assump_102 =>
                  apply Or.inl
                  intro assump_120
                  have assump_245 : (False → p2) := by
                    intro assump_127
                    apply False.elim assump_127
                  let assump_126 := assump_8 assump_245
                  apply False.elim assump_126
  intro assump_133
  cases assump_1
  case intro assump_136 assump_137 =>
    cases assump_136
    case intro assump_138 assump_139 =>
      cases assump_138
      case intro assump_140 assump_141 =>
        cases assump_137
        case intro assump_148 assump_149 =>
          cases assump_148
          case inl assump_150 =>
            cases assump_150
            case intro assump_152 assump_153 =>
              cases assump_149
              case inl assump_158 =>
                have assump_246 : (False → p2) := by
                  intro assump_166
                  apply False.elim assump_166
                let assump_165 := assump_139 assump_246
                apply False.elim assump_165
              case inr assump_159 =>
                cases assump_159
                case inl assump_172 =>
                  have assump_247 : (False → p2) := by
                    intro assump_179
                    apply False.elim assump_179
                  let assump_178 := assump_139 assump_247
                  apply False.elim assump_178
                case inr assump_173 =>
                  have assump_248 : (False → p2) := by
                    intro assump_190
                    apply False.elim assump_190
                  let assump_189 := assump_139 assump_248
                  apply False.elim assump_189
          case inr assump_151 =>
            cases assump_151
            case intro assump_196 assump_197 =>
              cases assump_149
              case inl assump_202 =>
                have assump_249 : (False → p2) := by
                  intro assump_210
                  apply False.elim assump_210
                let assump_209 := assump_139 assump_249
                apply False.elim assump_209
              case inr assump_203 =>
                cases assump_203
                case inl assump_216 =>
                  have assump_250 : (False → p2) := by
                    intro assump_223
                    apply False.elim assump_223
                  let assump_222 := assump_139 assump_250
                  apply False.elim assump_222
                case inr assump_217 =>
                  have assump_251 : (False → p2) := by
                    intro assump_234
                    apply False.elim assump_234
                  let assump_233 := assump_139 assump_251
                  apply False.elim assump_233


variable (p7 p0 p3 p5 p2 p6 : Prop)
theorem file61_44378 : (((((p3 ∧ p5) ∧ (p6 ∨ p0)) ∨ ((False → p2) ∧ (False → p0))) ∨ (((p0 → False) → False) → False)) → ((((True ∧ p2) ∧ (p0 ∧ False)) → False) ∨ (((p6 → p3) → False) ∧ ((True → False) ∨ (p7 → p0))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_7
          case inl assump_14 =>
            apply Or.inl
            intro assump_18
            cases assump_18
            case intro assump_19 assump_20 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                cases assump_20
                case intro assump_27 assump_28 =>
                  apply False.elim assump_28
          case inr assump_15 =>
            apply Or.inl
            intro assump_35
            cases assump_35
            case intro assump_36 assump_37 =>
              cases assump_36
              case intro assump_38 assump_39 =>
                cases assump_37
                case intro assump_44 assump_45 =>
                  apply False.elim assump_45
    case inr assump_5 =>
      cases assump_5
      case intro assump_50 assump_51 =>
        apply Or.inl
        intro assump_56
        cases assump_56
        case intro assump_57 assump_58 =>
          cases assump_57
          case intro assump_59 assump_60 =>
            cases assump_58
            case intro assump_65 assump_66 =>
              apply False.elim assump_66
  case inr assump_3 =>
    apply Or.inl
    intro assump_73
    cases assump_73
    case intro assump_74 assump_75 =>
      cases assump_74
      case intro assump_76 assump_77 =>
        cases assump_75
        case intro assump_82 assump_83 =>
          apply False.elim assump_83


variable (p4 p1 p2 p7 p5 p0 p6 : Prop)
theorem file61_46283 : (((((p2 → False) ∧ (p7 ∧ p2)) ∧ ((p1 → False) → False)) → (((False → False) ∨ (p0 ∨ p1)) ∨ ((p1 → False) → False))) ∨ ((((p1 ∧ p5) ∨ (p4 ∨ p4)) ∨ ((p6 ∧ p1) → (False ∨ p5))) ∧ (((p5 → False) → (p0 ∨ p0)) ∧ ((True → False) ∧ (p0 ∧ p5))))) := by
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
        apply False.elim assump_16


variable (p3 p5 p1 p4 p0 p2 p6 p7 : Prop)
theorem file61_46891 : (((((p6 ∧ p7) ∧ (p3 ∧ p2)) ∨ ((p1 ∧ p4) → False)) → (((p7 ∧ False) → False) ∨ ((True ∨ p0) → False))) ∨ ((((p5 ∧ p2) ∨ (True ∧ True)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
  case inr assump_3 =>
    apply Or.inl
    intro assump_27
    cases assump_27
    case intro assump_28 assump_29 =>
      apply False.elim assump_29


variable (p2 p1 p4 p0 p5 p6 p3 p7 : Prop)
theorem file61_47676 : ((((((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) → False) ∧ ((((p0 ∧ p4) ∨ (p5 ∧ p4)) ∧ ((p5 ∨ p6) ∧ (p2 → False))) ∧ (((p1 ∧ p7) → False) ∨ ((p6 ∨ p3) ∨ (p5 ∨ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_9
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_7
                case inl assump_26 =>
                  have assump_300 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                    apply And.intro
                    apply Or.inl
                    apply Or.inl
                    exact assump_20
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_35 := assump_2 assump_300
                  apply False.elim assump_35
                case inr assump_27 =>
                  cases assump_27
                  case inl assump_39 =>
                    cases assump_39
                    case inl assump_41 =>
                      have assump_301 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_20
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_50 := assump_2 assump_301
                      apply False.elim assump_50
                    case inr assump_42 =>
                      have assump_302 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_20
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_61 := assump_2 assump_302
                      apply False.elim assump_61
                  case inr assump_40 =>
                    cases assump_40
                    case inl assump_65 =>
                      have assump_303 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_65
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_74 := assump_2 assump_303
                      apply False.elim assump_74
                    case inr assump_66 =>
                      have assump_304 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_20
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_85 := assump_2 assump_304
                      apply False.elim assump_85
              case inr assump_21 =>
                cases assump_7
                case inl assump_93 =>
                  have assump_305 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                    apply And.intro
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_102 := assump_2 assump_305
                  apply False.elim assump_102
                case inr assump_94 =>
                  cases assump_94
                  case inl assump_106 =>
                    cases assump_106
                    case inl assump_108 =>
                      have assump_306 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_117 := assump_2 assump_306
                      apply False.elim assump_117
                    case inr assump_109 =>
                      have assump_307 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_128 := assump_2 assump_307
                      apply False.elim assump_128
                  case inr assump_107 =>
                    cases assump_107
                    case inl assump_132 =>
                      have assump_308 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_132
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_141 := assump_2 assump_308
                      apply False.elim assump_141
                    case inr assump_133 =>
                      have assump_309 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inr
                        apply True.intro
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_152 := assump_2 assump_309
                      apply False.elim assump_152
        case inr assump_11 =>
          cases assump_11
          case intro assump_156 assump_157 =>
            cases assump_9
            case intro assump_162 assump_163 =>
              cases assump_162
              case inl assump_164 =>
                cases assump_7
                case inl assump_170 =>
                  have assump_310 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                    apply And.intro
                    apply Or.inl
                    apply Or.inl
                    exact assump_164
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_179 := assump_2 assump_310
                  apply False.elim assump_179
                case inr assump_171 =>
                  cases assump_171
                  case inl assump_183 =>
                    cases assump_183
                    case inl assump_185 =>
                      have assump_311 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_164
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_194 := assump_2 assump_311
                      apply False.elim assump_194
                    case inr assump_186 =>
                      have assump_312 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_164
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_205 := assump_2 assump_312
                      apply False.elim assump_205
                  case inr assump_184 =>
                    cases assump_184
                    case inl assump_209 =>
                      have assump_313 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_209
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_218 := assump_2 assump_313
                      apply False.elim assump_218
                    case inr assump_210 =>
                      have assump_314 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_164
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_229 := assump_2 assump_314
                      apply False.elim assump_229
              case inr assump_165 =>
                cases assump_7
                case inl assump_237 =>
                  have assump_315 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                    apply And.intro
                    apply Or.inl
                    apply Or.inl
                    exact assump_156
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_246 := assump_2 assump_315
                  apply False.elim assump_246
                case inr assump_238 =>
                  cases assump_238
                  case inl assump_250 =>
                    cases assump_250
                    case inl assump_252 =>
                      have assump_316 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_156
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_261 := assump_2 assump_316
                      apply False.elim assump_261
                    case inr assump_253 =>
                      have assump_317 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_156
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_272 := assump_2 assump_317
                      apply False.elim assump_272
                  case inr assump_251 =>
                    cases assump_251
                    case inl assump_276 =>
                      have assump_318 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_276
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_285 := assump_2 assump_318
                      apply False.elim assump_285
                    case inr assump_277 =>
                      have assump_319 : (((p5 ∨ True) ∨ (p0 ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p0))) := by
                        apply And.intro
                        apply Or.inl
                        apply Or.inl
                        exact assump_156
                        apply Or.inl
                        apply Or.inl
                        apply True.intro
                      let assump_296 := assump_2 assump_319
                      apply False.elim assump_296


variable (p7 p5 : Prop)
theorem file61_60060 : (((((p5 → False) ∧ (p7 → False)) → ((p7 → True) ∧ (False → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((p5 → False) ∧ (p7 → False)) → ((p7 → True) ∧ (False → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    apply True.intro
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p2 p3 p5 p6 p1 p0 p4 : Prop)
theorem file61_60519 : (((((True → p1) ∨ (p7 → False)) ∧ ((p2 → False) → False)) → (((p3 ∧ False) → (p4 ∧ p6)) ∨ ((True ∨ p6) → False))) ∨ ((((p3 → False) ∧ (True ∧ p6)) ∨ ((p5 ∨ p0) → (p6 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_10
      apply And.intro
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
      cases assump_10
      case intro assump_17 assump_18 =>
        apply False.elim assump_18
    case inr assump_5 =>
      apply Or.inl
      intro assump_27
      apply And.intro
      cases assump_27
      case intro assump_28 assump_29 =>
        apply False.elim assump_29
      cases assump_27
      case intro assump_34 assump_35 =>
        apply False.elim assump_35


variable (p3 p6 p1 p7 p2 p4 : Prop)
theorem file61_61438 : (((((p4 → False) → (p4 → False)) ∧ ((p2 → True) → False)) → (((p6 → p7) → (p3 ∧ p1)) → False)) ∨ ((((False → p6) ∧ (p1 → False)) → ((True → p7) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_16 : (p2 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_6 assump_16
    apply False.elim assump_11


variable (p6 p0 p1 p7 p5 p3 p4 : Prop)
theorem file61_61926 : (((((p0 → p5) ∧ (p1 ∧ False)) ∧ ((p7 → False) ∧ (p4 → False))) → (((False → p5) ∨ (True ∨ p4)) ∨ ((p1 ∧ p6) → (p1 → False)))) ∨ ((((p0 ∧ p1) → (False → p1)) → False) ∨ (((False → False) ∨ (p0 → p7)) ∧ ((p3 ∨ p0) ∨ (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply False.elim assump_9


variable (p2 p1 : Prop)
theorem file61_62442 : (((((True → False) ∧ (p2 ∨ p1)) → False) → False) → False) := by
  intro assump_1
  have assump_29 : (((True → False) ∧ (p2 ∨ p1)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_30 : True := by
          apply True.intro
        let assump_15 := assump_6 assump_30
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_31 : True := by
          apply True.intro
        let assump_22 := assump_6 assump_31
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p5 p1 p4 p7 p2 p3 p0 : Prop)
theorem file61_63151 : (((((p1 ∨ p1) → (p2 ∧ p5)) → False) → False) → ((((p1 → False) → (p2 → True)) ∨ ((p5 → p0) → (p3 ∧ p2))) ∨ (((True ∧ p4) ∧ (p7 → p5)) → ((False ∧ p3) ∧ (p1 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p2 p0 p3 p4 p7 p1 : Prop)
theorem file61_63486 : ((((((True ∨ p4) ∨ (p0 ∧ p2)) → False) → (((p1 ∨ p7) ∧ (p0 → False)) → ((p3 ∨ p7) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((True ∨ p4) ∨ (p0 ∧ p2)) → False) → (((p1 ∨ p7) ∧ (p0 → False)) → ((p3 ∨ p7) ∨ (p0 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inr
        intro assump_17
        have assump_35 : ((True ∨ p4) ∨ (p0 ∧ p2)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_21 := assump_5 assump_35
        apply False.elim assump_21
      case inr assump_10 =>
        apply Or.inl
        apply Or.inr
        exact assump_10
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p0 p6 p3 p5 p1 p7 p4 p2 : Prop)
theorem file61_64370 : (((((p0 → p4) → False) → False) ∧ (((p1 → False) ∧ (p1 ∨ False)) ∨ ((p3 → p5) → False))) → ((((False ∨ False) → (p6 → p7)) ∨ ((p1 ∨ p5) → (p3 ∨ p6))) ∨ (((p3 ∨ p2) → False) ∧ ((p1 ∧ p1) → (p6 ∨ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          apply Or.inl
          apply Or.inl
          intro assump_16
          intro assump_17
          cases assump_16
          case inl assump_20 =>
            apply False.elim assump_20
          case inr assump_21 =>
            apply False.elim assump_21
        case inr assump_13 =>
          apply False.elim assump_13
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_30
      intro assump_31
      cases assump_30
      case inl assump_34 =>
        apply False.elim assump_34
      case inr assump_35 =>
        apply False.elim assump_35


variable (p5 p2 p6 p0 p1 : Prop)
theorem file61_65447 : (((((p5 → p5) ∧ (p6 ∨ p0)) ∧ ((p6 ∨ False) ∧ (p0 ∧ False))) ∧ (((p1 → p2) → (p0 → p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_15
              case intro assump_20 assump_21 =>
                apply False.elim assump_21
            case inr assump_17 =>
              apply False.elim assump_17
        case inr assump_11 =>
          cases assump_5
          case intro assump_30 assump_31 =>
            cases assump_30
            case inl assump_32 =>
              cases assump_31
              case intro assump_36 assump_37 =>
                apply False.elim assump_37
            case inr assump_33 =>
              apply False.elim assump_33


variable (p3 p7 p0 p6 p4 p1 p5 : Prop)
theorem file61_66541 : ((((((p4 → p1) → False) → False) → (((p0 ∨ p7) ∨ (p7 ∧ p7)) → ((p0 ∨ True) ∧ (p1 ∧ p7)))) ∧ ((((p6 → p3) → False) ∧ ((False ∧ False) ∧ (p7 → p6))) ∧ (((p5 → False) → False) ∨ ((False ∧ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14


variable (p0 p6 p1 p2 p5 : Prop)
theorem file61_67170 : (((((True → False) ∨ (p2 ∨ p5)) → False) → False) → ((((True ∨ False) → False) → ((p1 ∨ p1) ∧ (p0 ∧ True))) ∨ (((p0 → False) ∨ (p6 ∧ p6)) ∨ ((p5 ∧ p5) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  have assump_17 : (True ∨ False) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_4 assump_17
  apply False.elim assump_7
  apply And.intro
  have assump_18 : (True ∨ False) := by
    apply Or.inl
    apply True.intro
  let assump_13 := assump_4 assump_18
  apply False.elim assump_13
  apply True.intro


variable (p7 p4 p2 p1 p3 p0 p6 : Prop)
theorem file61_67794 : (((((p4 ∧ p4) ∧ (p6 ∨ p1)) → False) ∧ (((p4 ∨ p3) ∨ (p7 → p0)) → False)) → ((((p2 ∧ p0) → (False → p3)) → False) → (((p3 ∧ False) ∧ (p0 → True)) → ((p2 ∨ p4) ∨ (False → p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p5 p0 p3 p2 p7 : Prop)
theorem file61_68223 : ((((((p7 → False) ∨ (False ∨ True)) → ((False → False) ∨ (p2 → False))) ∧ (((p5 → p7) → (False → p0)) ∨ ((True ∧ p0) ∧ (True ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p7 → False) ∨ (False ∨ True)) → ((False → False) ∨ (p2 → False))) ∧ (((p5 → p7) → (False → p0)) ∨ ((True ∧ p0) ∧ (True ∨ p3)))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case inl assump_13 =>
        apply False.elim assump_13
      case inr assump_14 =>
        apply Or.inl
        intro assump_19
        apply False.elim assump_19
    apply Or.inl
    intro assump_22
    intro assump_23
    apply False.elim assump_23
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p0 p5 p2 p3 p6 p1 : Prop)
theorem file61_69142 : ((((((p5 ∨ p0) → (True → p1)) → False) ∧ (((p0 → True) ∨ (p6 → False)) → False)) ∧ ((((True ∨ p3) ∨ (p2 ∧ p0)) ∨ ((p5 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : (((True ∨ p3) ∨ (p2 ∧ p0)) ∨ ((p5 → False) → False)) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p7 p1 p6 p3 : Prop)
theorem file61_69726 : ((((((p7 → True) → False) ∧ ((False ∧ False) → False)) → False) → ((((True ∧ p3) ∨ (p1 ∨ True)) → False) ∧ (((True → False) → False) ∧ ((p6 → False) → (p3 ∧ True))))) → False) := by
  intro assump_1
  have assump_23 : ((((p7 → True) → False) ∧ ((False ∧ False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_24 : (p7 → True) := by
        intro assump_14
        apply True.intro
      let assump_13 := assump_6 assump_24
      apply False.elim assump_13
  let assump_4 := assump_1 assump_23
  let assump_18 := And.left assump_4
  have assump_25 : ((True ∧ p3) ∨ (p1 ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_19 := assump_18 assump_25
  apply False.elim assump_19


variable (p2 p3 p7 p4 p1 p0 p6 : Prop)
theorem file61_70564 : (((((False ∧ p1) → False) ∨ ((True → p4) → False)) ∨ (((p1 → False) ∨ (p3 ∨ p6)) → False)) ∨ ((((p2 ∨ p3) → (p0 ∧ p1)) → False) ∧ (((p7 ∨ p1) ∧ (False ∧ p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2


variable (p1 p4 p3 p0 p6 p2 p5 p7 : Prop)
theorem file61_70948 : (((((False → False) → False) ∧ ((False → p3) ∨ (p2 ∧ p6))) → (((p5 → False) → False) ∨ ((p0 ∨ p3) ∨ (False → p5)))) ∧ ((((p3 ∧ p2) ∧ (p2 ∨ p7)) → ((p4 → p4) ∧ (p0 ∧ p0))) → (((p6 → False) → (p6 → p7)) ∨ ((p0 ∨ p1) ∧ (False → p7))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      have assump_54 : (False → False) := by
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_2 assump_54
      apply False.elim assump_15
    case inr assump_7 =>
      cases assump_7
      case intro assump_22 assump_23 =>
        apply Or.inl
        intro assump_28
        have assump_55 : (False → False) := by
          intro assump_35
          apply False.elim assump_35
        let assump_34 := assump_2 assump_55
        apply False.elim assump_34
  intro assump_41
  apply Or.inl
  intro assump_44
  intro assump_45
  have assump_56 : p6 := by
    exact assump_45
  let assump_50 := assump_44 assump_56
  apply False.elim assump_50


variable (p2 p7 p6 p4 p0 p3 : Prop)
theorem file61_72102 : (((((p4 ∧ True) ∨ (p2 → False)) → ((p7 → p3) → (p0 → p6))) ∧ (((False → False) → (p4 ∨ True)) → False)) → ((((p4 ∧ p6) ∧ (p6 → p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_18 : ((False → False) → (p4 ∨ True)) := by
      intro assump_12
      apply Or.inr
      apply True.intro
    let assump_11 := assump_6 assump_18
    apply False.elim assump_11


variable (p2 p0 p6 p1 : Prop)
theorem file61_72592 : ((((((p6 ∧ False) ∨ (False ∨ p2)) ∨ ((p1 → p0) → (False → False))) → False) ∨ ((((True → False) ∨ (p2 → False)) → False) ∧ (((p2 → True) ∨ (True ∧ p2)) → False))) → False) := by
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    have assump_33 : (((p6 ∧ False) ∨ (False ∨ p2)) ∨ ((p1 → p0) → (False → False))) := by
      apply Or.inr
      intro assump_15
      intro assump_16
      apply False.elim assump_16
    let assump_14 := assump_10 assump_33
    apply False.elim assump_14
  case inr assump_11 =>
    cases assump_11
    case intro assump_22 assump_23 =>
      have assump_34 : ((p2 → True) ∨ (True ∧ p2)) := by
        apply Or.inl
        intro assump_29
        apply True.intro
      let assump_28 := assump_23 assump_34
      apply False.elim assump_28


variable (p0 p5 p6 p3 p4 p7 p2 : Prop)
theorem file61_73435 : (((((p5 ∧ p7) ∧ (p6 → False)) → ((p5 → False) → False)) → False) → ((((p0 ∧ p0) ∨ (p6 → p6)) ∨ ((p5 ∧ p6) ∧ (p2 ∨ p4))) → (((p5 → False) → (p3 ∨ p7)) ∨ ((p2 ∧ p0) ∧ (p7 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply Or.inl
        intro assump_15
        have assump_109 : (((p5 ∧ p7) ∧ (p6 → False)) → ((p5 → False) → False)) := by
          intro assump_20
          intro assump_21
          cases assump_20
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              have assump_110 : p5 := by
                exact assump_26
              let assump_37 := assump_21 assump_110
              apply False.elim assump_37
        let assump_19 := assump_1 assump_109
        apply False.elim assump_19
    case inr assump_6 =>
      apply Or.inl
      intro assump_48
      have assump_111 : (((p5 ∧ p7) ∧ (p6 → False)) → ((p5 → False) → False)) := by
        intro assump_53
        intro assump_54
        cases assump_53
        case intro assump_57 assump_58 =>
          cases assump_57
          case intro assump_59 assump_60 =>
            have assump_112 : p5 := by
              exact assump_59
            let assump_70 := assump_54 assump_112
            apply False.elim assump_70
      let assump_52 := assump_1 assump_111
      apply False.elim assump_52
  case inr assump_4 =>
    cases assump_4
    case intro assump_77 assump_78 =>
      cases assump_77
      case intro assump_79 assump_80 =>
        cases assump_78
        case inl assump_85 =>
          apply Or.inl
          intro assump_91
          have assump_113 : p5 := by
            exact assump_79
          let assump_94 := assump_91 assump_113
          apply False.elim assump_94
        case inr assump_86 =>
          apply Or.inl
          intro assump_102
          have assump_114 : p5 := by
            exact assump_79
          let assump_105 := assump_102 assump_114
          apply False.elim assump_105


variable (p6 p2 p5 p1 p3 p4 p0 : Prop)
theorem file61_75632 : ((((((p1 → p1) ∨ (p2 → False)) → ((p5 ∨ True) ∧ (p4 ∧ p6))) ∨ (((p6 → False) ∨ (False → p6)) → ((True ∨ p1) ∧ (p3 ∨ p5)))) ∧ ((((p4 ∧ p3) → (p4 ∧ True)) → False) ∧ (((True → p0) ∨ (p4 → False)) ∨ ((p3 → False) ∧ (False → False))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_13
        case inl assump_16 =>
          cases assump_16
          case inl assump_18 =>
            have assump_126 : ((p4 ∧ p3) → (p4 ∧ True)) := by
              intro assump_25
              apply And.intro
              cases assump_25
              case intro assump_26 assump_27 =>
                exact assump_26
              apply True.intro
            let assump_24 := assump_12 assump_126
            apply False.elim assump_24
          case inr assump_19 =>
            have assump_127 : ((p4 ∧ p3) → (p4 ∧ True)) := by
              intro assump_39
              apply And.intro
              cases assump_39
              case intro assump_40 assump_41 =>
                exact assump_40
              apply True.intro
            let assump_38 := assump_12 assump_127
            apply False.elim assump_38
        case inr assump_17 =>
          cases assump_17
          case intro assump_49 assump_50 =>
            have assump_128 : ((p4 ∧ p3) → (p4 ∧ True)) := by
              intro assump_58
              apply And.intro
              cases assump_58
              case intro assump_59 assump_60 =>
                exact assump_59
              apply True.intro
            let assump_57 := assump_12 assump_128
            apply False.elim assump_57
    case inr assump_9 =>
      cases assump_7
      case intro assump_70 assump_71 =>
        cases assump_71
        case inl assump_74 =>
          cases assump_74
          case inl assump_76 =>
            have assump_129 : ((p4 ∧ p3) → (p4 ∧ True)) := by
              intro assump_83
              apply And.intro
              cases assump_83
              case intro assump_84 assump_85 =>
                exact assump_84
              apply True.intro
            let assump_82 := assump_70 assump_129
            apply False.elim assump_82
          case inr assump_77 =>
            have assump_130 : ((p4 ∧ p3) → (p4 ∧ True)) := by
              intro assump_97
              apply And.intro
              cases assump_97
              case intro assump_98 assump_99 =>
                exact assump_98
              apply True.intro
            let assump_96 := assump_70 assump_130
            apply False.elim assump_96
        case inr assump_75 =>
          cases assump_75
          case intro assump_107 assump_108 =>
            have assump_131 : ((p4 ∧ p3) → (p4 ∧ True)) := by
              intro assump_116
              apply And.intro
              cases assump_116
              case intro assump_117 assump_118 =>
                exact assump_117
              apply True.intro
            let assump_115 := assump_70 assump_131
            apply False.elim assump_115


variable (p7 p2 p1 p0 p5 : Prop)
theorem file61_78804 : ((((((p7 ∧ p0) ∧ (p2 ∨ False)) ∨ ((p5 → p1) ∧ (True → False))) → (((True → False) ∧ (p0 ∨ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_88 : ((((p7 ∧ p0) ∧ (p2 ∨ False)) ∨ ((p5 → p1) ∧ (True → False))) → (((True → False) ∧ (p0 ∨ p7)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_5
        case inl assump_15 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_18
              case inl assump_25 =>
                have assump_89 : True := by
                  apply True.intro
                let assump_33 := assump_7 assump_89
                apply False.elim assump_33
              case inr assump_26 =>
                apply False.elim assump_26
        case inr assump_16 =>
          cases assump_16
          case intro assump_39 assump_40 =>
            have assump_90 : True := by
              apply True.intro
            let assump_45 := assump_40 assump_90
            apply False.elim assump_45
      case inr assump_12 =>
        cases assump_5
        case inl assump_51 =>
          cases assump_51
          case intro assump_53 assump_54 =>
            cases assump_53
            case intro assump_55 assump_56 =>
              cases assump_54
              case inl assump_61 =>
                have assump_91 : True := by
                  apply True.intro
                let assump_69 := assump_7 assump_91
                apply False.elim assump_69
              case inr assump_62 =>
                apply False.elim assump_62
        case inr assump_52 =>
          cases assump_52
          case intro assump_75 assump_76 =>
            have assump_92 : True := by
              apply True.intro
            let assump_81 := assump_76 assump_92
            apply False.elim assump_81
  let assump_4 := assump_1 assump_88
  apply False.elim assump_4


variable (p4 p2 p0 p5 p3 p7 p1 p6 : Prop)
theorem file61_80929 : ((((((True ∧ p7) → (True → False)) → False) ∨ (((p4 ∧ p4) → False) ∧ ((False ∧ p1) → (p6 → p1)))) ∧ ((((p7 ∧ p7) → False) ∧ ((p5 ∧ p7) ∧ (p4 ∨ p2))) ∧ (((p0 → p6) → (p3 → False)) ∧ ((p7 → True) → (p6 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_15
              case inl assump_22 =>
                cases assump_9
                case intro assump_26 assump_27 =>
                  have assump_106 : (p7 → True) := by
                    intro assump_33
                    apply True.intro
                  let assump_32 := assump_27 assump_106
                  let assump_34 := And.right assump_32
                  apply False.elim assump_34
              case inr assump_23 =>
                cases assump_9
                case intro assump_41 assump_42 =>
                  have assump_107 : (p7 → True) := by
                    intro assump_48
                    apply True.intro
                  let assump_47 := assump_42 assump_107
                  let assump_49 := And.right assump_47
                  apply False.elim assump_49
    case inr assump_5 =>
      cases assump_5
      case intro assump_54 assump_55 =>
        cases assump_3
        case intro assump_60 assump_61 =>
          cases assump_60
          case intro assump_62 assump_63 =>
            cases assump_63
            case intro assump_66 assump_67 =>
              cases assump_66
              case intro assump_68 assump_69 =>
                cases assump_67
                case inl assump_74 =>
                  cases assump_61
                  case intro assump_78 assump_79 =>
                    have assump_108 : (p7 → True) := by
                      intro assump_85
                      apply True.intro
                    let assump_84 := assump_79 assump_108
                    let assump_86 := And.right assump_84
                    apply False.elim assump_86
                case inr assump_75 =>
                  cases assump_61
                  case intro assump_93 assump_94 =>
                    have assump_109 : (p7 → True) := by
                      intro assump_100
                      apply True.intro
                    let assump_99 := assump_94 assump_109
                    let assump_101 := And.right assump_99
                    apply False.elim assump_101


variable (p4 p2 p6 p3 p0 p5 p7 : Prop)
theorem file61_83676 : (((((p6 → p0) → False) → ((p4 ∨ True) ∨ (p3 → p5))) → False) → ((((p0 ∨ p2) → False) → False) ∨ (((p5 → False) ∨ (False → False)) ∧ ((p4 ∧ p7) ∧ (p2 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_15 : (((p6 → p0) → False) → ((p4 ∨ True) ∨ (p3 → p5))) := by
    intro assump_9
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_8 := assump_1 assump_15
  apply False.elim assump_8


variable (p5 p7 p2 p6 p4 p0 : Prop)
theorem file61_84167 : ((((((p6 ∨ False) → (p6 ∧ p7)) ∧ ((p0 → False) ∧ (p7 → False))) ∧ (((p5 ∨ p7) ∧ (p7 → p0)) ∧ ((p5 ∨ p7) → False))) ∧ ((((False ∧ False) ∧ (False ∨ p4)) ∧ ((False → p5) ∧ (False ∧ p6))) ∧ (((p5 ∧ True) ∨ (p7 → p2)) → False))) → False) := by
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
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_3
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case intro assump_34 assump_35 =>
                        apply False.elim assump_34
              case inr assump_21 =>
                cases assump_3
                case intro assump_44 assump_45 =>
                  cases assump_44
                  case intro assump_46 assump_47 =>
                    cases assump_46
                    case intro assump_48 assump_49 =>
                      cases assump_48
                      case intro assump_50 assump_51 =>
                        apply False.elim assump_50


variable (p5 p6 p4 p3 p2 p0 p1 p7 : Prop)
theorem file61_85769 : (((((p1 ∨ p7) ∨ (p0 ∧ p3)) → False) ∧ (((p3 ∨ True) → False) ∧ ((p2 ∧ p6) ∨ (p1 → False)))) → ((((p6 ∧ True) ∧ (p0 ∧ False)) → ((False → p4) → (p2 → p6))) ∧ (((p0 → p5) ∧ (p1 ∨ p1)) ∨ ((p1 → False) → (p1 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_10
      case intro assump_17 assump_18 =>
        apply False.elim assump_18
  cases assump_1
  case intro assump_23 assump_24 =>
    cases assump_24
    case intro assump_27 assump_28 =>
      cases assump_28
      case inl assump_31 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          apply Or.inr
          intro assump_49
          intro assump_50
          have assump_80 : p1 := by
            exact assump_50
          let assump_55 := assump_49 assump_80
          apply False.elim assump_55
      case inr assump_32 =>
        apply Or.inr
        intro assump_70
        intro assump_71
        have assump_81 : p1 := by
          exact assump_71
        let assump_76 := assump_70 assump_81
        apply False.elim assump_76


variable (p1 p4 p3 p6 p5 p0 p2 : Prop)
theorem file61_87034 : (((((p3 → False) → (p3 → False)) → ((p0 ∨ p5) → (True ∨ p3))) ∨ (((True → p1) ∨ (p2 ∨ p5)) → False)) ∨ ((((p0 ∨ p6) → (p4 → p1)) → False) ∨ (((p6 → False) → (p0 → False)) ∧ ((p3 ∧ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    apply True.intro
  case inr assump_4 =>
    apply Or.inl
    apply True.intro


variable (p7 p5 p4 p0 p3 : Prop)
theorem file61_87498 : ((((((p0 → False) ∧ (p0 ∨ p3)) ∧ ((p7 → p5) ∧ (p0 ∨ p0))) → (((p0 → p3) → False) ∨ ((True ∧ p5) ∨ (True → p4)))) → False) → False) := by
  intro assump_1
  have assump_89 : ((((p0 → False) ∧ (p0 ∨ p3)) ∧ ((p7 → p5) ∧ (p0 ∨ p0))) → (((p0 → p3) → False) ∨ ((True ∧ p5) ∨ (True → p4)))) := by
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
            case inl assump_20 =>
              apply Or.inl
              intro assump_24
              have assump_90 : p0 := by
                exact assump_20
              let assump_32 := assump_8 assump_90
              apply False.elim assump_32
            case inr assump_21 =>
              apply Or.inl
              intro assump_38
              have assump_91 : p0 := by
                exact assump_21
              let assump_46 := assump_8 assump_91
              apply False.elim assump_46
        case inr assump_13 =>
          cases assump_7
          case intro assump_52 assump_53 =>
            cases assump_53
            case inl assump_56 =>
              apply Or.inl
              intro assump_60
              have assump_92 : p0 := by
                exact assump_56
              let assump_68 := assump_8 assump_92
              apply False.elim assump_68
            case inr assump_57 =>
              apply Or.inl
              intro assump_74
              have assump_93 : p0 := by
                exact assump_57
              let assump_82 := assump_8 assump_93
              apply False.elim assump_82
  let assump_4 := assump_1 assump_89
  apply False.elim assump_4


variable (p7 p0 p6 p4 : Prop)
theorem file61_89333 : (((((p6 → False) ∨ (p7 → False)) ∧ ((True ∨ p0) → False)) ∧ (((p7 ∧ p4) → (True ∧ p4)) → ((False ∧ p6) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_46 : (True ∨ p0) := by
          apply Or.inl
          apply True.intro
        let assump_23 := assump_5 assump_46
        apply False.elim assump_23
      case inr assump_7 =>
        have assump_47 : (True ∨ p0) := by
          apply Or.inl
          apply True.intro
        let assump_42 := assump_5 assump_47
        apply False.elim assump_42


variable (p2 p7 p3 p6 p1 : Prop)
theorem file61_90061 : ((((((p3 ∧ p7) → (p6 ∧ False)) → ((p2 → True) → (True ∨ True))) ∨ (((p1 → p6) ∧ (True ∨ False)) → False)) → False) → False) := by
  intro assump_17
  have assump_30 : ((((p3 ∧ p7) → (p6 ∧ False)) → ((p2 → True) → (True ∨ True))) ∨ (((p1 → p6) ∧ (True ∨ False)) → False)) := by
    apply Or.inl
    intro assump_21
    intro assump_22
    apply Or.inl
    apply True.intro
  let assump_20 := assump_17 assump_30
  apply False.elim assump_20


variable (p1 p7 p4 p0 p3 : Prop)
theorem file61_90558 : ((((((p4 → True) → False) → False) → False) ∧ ((((p7 → True) ∧ (p1 ∨ p7)) → ((p1 ∧ p3) → (True → False))) ∨ (((p3 ∧ p7) → (p4 → p1)) ∨ ((False ∨ p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_56 : (((p4 → True) → False) → False) := by
        intro assump_13
        have assump_57 : (p4 → True) := by
          intro assump_17
          apply True.intro
        let assump_16 := assump_13 assump_57
        apply False.elim assump_16
      let assump_12 := assump_2 assump_56
      apply False.elim assump_12
    case inr assump_7 =>
      cases assump_7
      case inl assump_24 =>
        have assump_58 : (((p4 → True) → False) → False) := by
          intro assump_30
          have assump_59 : (p4 → True) := by
            intro assump_34
            apply True.intro
          let assump_33 := assump_30 assump_59
          apply False.elim assump_33
        let assump_29 := assump_2 assump_58
        apply False.elim assump_29
      case inr assump_25 =>
        have assump_60 : (((p4 → True) → False) → False) := by
          intro assump_45
          have assump_61 : (p4 → True) := by
            intro assump_49
            apply True.intro
          let assump_48 := assump_45 assump_61
          apply False.elim assump_48
        let assump_44 := assump_2 assump_60
        apply False.elim assump_44


variable (p2 p0 p7 p6 : Prop)
theorem file61_92046 : (((((p0 → False) ∧ (False ∧ p2)) → ((p6 ∨ p7) → False)) → False) → False) := by
  intro assump_11
  have assump_42 : (((p0 → False) ∧ (False ∧ p2)) → ((p6 ∨ p7) → False)) := by
    intro assump_15
    intro assump_16
    cases assump_16
    case inl assump_17 =>
      cases assump_15
      case intro assump_21 assump_22 =>
        cases assump_22
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
    case inr assump_18 =>
      cases assump_15
      case intro assump_31 assump_32 =>
        cases assump_32
        case intro assump_35 assump_36 =>
          apply False.elim assump_35
  let assump_14 := assump_11 assump_42
  apply False.elim assump_14


variable (p1 p4 p5 p3 p6 p7 p2 : Prop)
theorem file61_92796 : (((((p7 ∨ p1) → False) ∨ ((True → p7) → (p6 ∧ p2))) ∨ (((p1 ∧ True) ∨ (p5 → p1)) ∧ ((p1 → False) → False))) → ((((p7 → False) ∨ (True ∨ p3)) → ((p4 → True) ∨ (p1 → False))) → (((p7 ∧ p1) ∧ (False ∧ p1)) → False))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_9
      case intro assump_16 assump_17 =>
        apply False.elim assump_16


variable (p1 p2 p7 p0 p6 p4 p3 p5 : Prop)
theorem file61_93337 : ((((((p0 ∧ p5) ∧ (False ∨ True)) → ((p4 → p4) ∧ (p6 → p2))) → (((p5 → p7) ∨ (p3 → p1)) → False)) ∧ ((((p1 → p0) ∨ (p1 ∧ p4)) → ((p6 ∧ p6) → (p6 ∨ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_30 : (((p1 → p0) ∨ (p1 ∧ p4)) → ((p6 ∧ p6) → (p6 ∨ p7))) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_9
        case inl assump_17 =>
          apply Or.inl
          exact assump_12
        case inr assump_18 =>
          cases assump_18
          case intro assump_21 assump_22 =>
            apply Or.inl
            exact assump_12
    let assump_8 := assump_3 assump_30
    apply False.elim assump_8


variable (p2 p3 p0 p4 p5 p7 p1 p6 : Prop)
theorem file61_94156 : (((((p2 ∨ p2) ∧ (p1 ∨ p3)) ∧ ((p2 → False) ∧ (p1 ∨ p7))) → False) ∨ ((((p6 → p0) ∨ (p5 → p2)) ∧ ((p2 → p1) ∨ (p7 ∧ p4))) → (((True → False) ∧ (p4 ∨ True)) → False))) := by
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
            case inl assump_18 =>
              have assump_104 : p2 := by
                exact assump_6
              let assump_23 := assump_14 assump_104
              apply False.elim assump_23
            case inr assump_19 =>
              have assump_105 : p2 := by
                exact assump_6
              let assump_30 := assump_14 assump_105
              apply False.elim assump_30
        case inr assump_11 =>
          cases assump_3
          case intro assump_36 assump_37 =>
            cases assump_37
            case inl assump_40 =>
              have assump_106 : p2 := by
                exact assump_6
              let assump_45 := assump_36 assump_106
              apply False.elim assump_45
            case inr assump_41 =>
              have assump_107 : p2 := by
                exact assump_6
              let assump_52 := assump_36 assump_107
              apply False.elim assump_52
      case inr assump_7 =>
        cases assump_5
        case inl assump_58 =>
          cases assump_3
          case intro assump_62 assump_63 =>
            cases assump_63
            case inl assump_66 =>
              have assump_108 : p2 := by
                exact assump_7
              let assump_71 := assump_62 assump_108
              apply False.elim assump_71
            case inr assump_67 =>
              have assump_109 : p2 := by
                exact assump_7
              let assump_78 := assump_62 assump_109
              apply False.elim assump_78
        case inr assump_59 =>
          cases assump_3
          case intro assump_84 assump_85 =>
            cases assump_85
            case inl assump_88 =>
              have assump_110 : p2 := by
                exact assump_7
              let assump_93 := assump_84 assump_110
              apply False.elim assump_93
            case inr assump_89 =>
              have assump_111 : p2 := by
                exact assump_7
              let assump_100 := assump_84 assump_111
              apply False.elim assump_100


variable (p3 p6 p5 p1 : Prop)
theorem file61_96743 : ((((((p6 → False) ∧ (False ∧ p1)) → False) ∨ (((p3 → p1) → False) ∧ ((True → False) → False))) → ((((True → False) → (True → False)) → False) ∧ (((p3 → False) ∧ (False → p5)) → False))) → False) := by
  intro assump_1
  have assump_29 : ((((p6 → False) ∧ (False ∧ p1)) → False) ∨ (((p3 → p1) → False) ∧ ((True → False) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_29
  let assump_14 := And.left assump_4
  have assump_30 : ((True → False) → (True → False)) := by
    intro assump_16
    intro assump_17
    have assump_31 : True := by
      apply True.intro
    let assump_22 := assump_16 assump_31
    apply False.elim assump_22
  let assump_15 := assump_14 assump_30
  apply False.elim assump_15


variable (p4 p1 p7 p6 p3 : Prop)
theorem file61_97691 : ((((((p7 ∨ p6) ∨ (p7 → p7)) → ((p7 → p3) → (False → p3))) ∨ (((p6 ∧ p7) ∧ (False ∧ p1)) ∨ ((True ∨ p4) → False))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p7 ∨ p6) ∨ (p7 → p7)) → ((p7 → p3) → (False → p3))) ∨ (((p6 ∧ p7) ∧ (False ∧ p1)) ∨ ((True ∨ p4) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p2 p7 p6 p3 p0 p1 p4 : Prop)
theorem file61_98215 : (((((p7 ∧ p0) → (p2 → p0)) ∧ ((p2 ∨ p7) → (True ∨ True))) → False) → ((((p1 ∨ p1) ∧ (p3 → p6)) → False) ∧ (((p0 → p4) → False) → ((True → p2) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      have assump_90 : (((p7 ∧ p0) → (p2 → p0)) ∧ ((p2 ∨ p7) → (True ∨ True))) := by
        apply And.intro
        intro assump_14
        intro assump_15
        cases assump_14
        case intro assump_18 assump_19 =>
          exact assump_19
        intro assump_24
        cases assump_24
        case inl assump_25 =>
          apply Or.inl
          apply True.intro
        case inr assump_26 =>
          apply Or.inl
          apply True.intro
      let assump_13 := assump_1 assump_90
      apply False.elim assump_13
    case inr assump_6 =>
      have assump_91 : (((p7 ∧ p0) → (p2 → p0)) ∧ ((p2 ∨ p7) → (True ∨ True))) := by
        apply And.intro
        intro assump_41
        intro assump_42
        cases assump_41
        case intro assump_45 assump_46 =>
          exact assump_46
        intro assump_51
        cases assump_51
        case inl assump_52 =>
          apply Or.inl
          apply True.intro
        case inr assump_53 =>
          apply Or.inl
          apply True.intro
      let assump_40 := assump_1 assump_91
      apply False.elim assump_40
  intro assump_61
  intro assump_62
  have assump_92 : (((p7 ∧ p0) → (p2 → p0)) ∧ ((p2 ∨ p7) → (True ∨ True))) := by
    apply And.intro
    intro assump_70
    intro assump_71
    cases assump_70
    case intro assump_74 assump_75 =>
      exact assump_75
    intro assump_80
    cases assump_80
    case inl assump_81 =>
      apply Or.inl
      apply True.intro
    case inr assump_82 =>
      apply Or.inl
      apply True.intro
  let assump_69 := assump_1 assump_92
  apply False.elim assump_69


variable (p5 p7 p3 p4 p1 p2 : Prop)
theorem file61_100171 : ((((((p3 ∧ p1) ∨ (p3 → False)) ∨ ((p7 → True) ∧ (False → False))) ∧ (((p1 → True) → False) → False)) ∧ ((((p4 → False) ∧ (p7 ∧ p4)) → ((p5 ∧ p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            have assump_120 : (((p4 → False) ∧ (p7 ∧ p4)) → ((p5 ∧ p2) → False)) := by
              intro assump_21
              intro assump_22
              cases assump_22
              case intro assump_23 assump_24 =>
                cases assump_21
                case intro assump_29 assump_30 =>
                  cases assump_30
                  case intro assump_33 assump_34 =>
                    have assump_121 : p4 := by
                      exact assump_34
                    let assump_41 := assump_29 assump_121
                    apply False.elim assump_41
            let assump_20 := assump_3 assump_120
            apply False.elim assump_20
        case inr assump_9 =>
          have assump_122 : (((p4 → False) ∧ (p7 ∧ p4)) → ((p5 ∧ p2) → False)) := by
            intro assump_55
            intro assump_56
            cases assump_56
            case intro assump_57 assump_58 =>
              cases assump_55
              case intro assump_63 assump_64 =>
                cases assump_64
                case intro assump_67 assump_68 =>
                  have assump_123 : p4 := by
                    exact assump_68
                  let assump_75 := assump_63 assump_123
                  apply False.elim assump_75
          let assump_54 := assump_3 assump_122
          apply False.elim assump_54
      case inr assump_7 =>
        cases assump_7
        case intro assump_82 assump_83 =>
          have assump_124 : (((p4 → False) ∧ (p7 ∧ p4)) → ((p5 ∧ p2) → False)) := by
            intro assump_93
            intro assump_94
            cases assump_94
            case intro assump_95 assump_96 =>
              cases assump_93
              case intro assump_101 assump_102 =>
                cases assump_102
                case intro assump_105 assump_106 =>
                  have assump_125 : p4 := by
                    exact assump_106
                  let assump_113 := assump_101 assump_125
                  apply False.elim assump_113
          let assump_92 := assump_3 assump_124
          apply False.elim assump_92


variable (p5 p4 p6 p2 : Prop)
theorem file61_102780 : (((((p4 ∨ p5) ∨ (p6 → False)) → False) ∧ (((True ∨ p2) ∨ (p4 ∧ p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((True ∨ p2) ∨ (p4 ∧ p6)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p6 p3 : Prop)
theorem file61_103172 : ((((((True ∨ True) ∨ (p3 → False)) → False) → (((p6 → False) → False) ∨ ((True → False) → False))) → False) → False) := by
  intro assump_5
  have assump_23 : ((((True ∨ True) ∨ (p3 → False)) → False) → (((p6 → False) → False) ∨ ((True → False) → False))) := by
    intro assump_9
    apply Or.inl
    intro assump_12
    have assump_24 : ((True ∨ True) ∨ (p3 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_16 := assump_9 assump_24
    apply False.elim assump_16
  let assump_8 := assump_5 assump_23
  apply False.elim assump_8


variable (p5 p2 p4 p0 p3 p6 p1 p7 : Prop)
theorem file61_103811 : (((((p5 ∨ p7) ∧ (True ∨ p6)) ∧ ((True → False) ∧ (p1 ∧ False))) ∨ (((False ∧ True) ∧ (p2 ∧ p0)) → False)) ∨ ((((p6 → p5) → False) ∧ ((p0 ∧ p4) → (True ∨ p3))) ∨ (((p5 ∨ p7) → False) → False))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4


variable (p2 p7 p1 p3 p6 p0 p5 : Prop)
theorem file61_104258 : ((((((p5 ∨ p6) → False) ∨ ((p0 ∨ p3) ∨ (True → False))) → False) ∧ ((((p7 ∧ p1) ∧ (p7 → p3)) ∨ ((True → p3) → (p5 → p2))) ∧ (((p1 ∨ False) ∨ (p3 → p3)) → False))) → False) := by
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
            have assump_37 : ((p1 ∨ False) ∨ (p3 → p3)) := by
              apply Or.inl
              apply Or.inl
              exact assump_13
            let assump_22 := assump_7 assump_37
            apply False.elim assump_22
      case inr assump_9 =>
        have assump_38 : ((p1 ∨ False) ∨ (p3 → p3)) := by
          apply Or.inr
          intro assump_31
          exact assump_31
        let assump_30 := assump_7 assump_38
        apply False.elim assump_30


variable (p3 p5 p0 p7 p4 p6 p2 p1 : Prop)
theorem file61_105280 : (((((p5 ∧ False) ∧ (p1 ∨ p3)) → False) → (((p4 ∧ False) ∧ (p0 → p2)) ∧ ((p5 → p4) → (p0 → p1)))) → ((((p0 ∧ p7) → (p3 ∨ p3)) → False) ∨ (((p3 ∧ p6) → False) ∧ ((True ∨ p7) ∨ (p2 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_25 : (((p5 ∧ False) ∧ (p1 ∨ p3)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
  let assump_8 := assump_1 assump_25
  let assump_18 := And.left assump_8
  let assump_19 := And.left assump_18
  let assump_20 := And.right assump_19
  apply False.elim assump_20


variable (p4 p1 p5 p3 p2 p0 : Prop)
theorem file61_106001 : ((((((p1 → p3) → False) ∨ ((p2 → False) → False)) ∧ (((p1 ∧ False) ∧ (p2 ∨ p4)) ∧ ((p2 ∧ False) ∧ (p1 → p5)))) ∧ ((((True ∧ p4) → False) → False) ∨ (((p0 → p4) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              apply False.elim assump_15
      case inr assump_7 =>
        cases assump_5
        case intro assump_22 assump_23 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              apply False.elim assump_27


variable (p6 p1 p3 p5 : Prop)
theorem file61_106948 : ((((((False ∨ True) ∨ (p1 ∨ p3)) ∨ ((p5 ∨ p3) ∨ (p5 → False))) ∨ (((p1 ∧ p5) → (p6 ∧ p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : ((((False ∨ True) ∨ (p1 ∨ p3)) ∨ ((p5 ∨ p3) ∨ (p5 → False))) ∨ (((p1 ∧ p5) → (p6 ∧ p3)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p1 p2 p5 p7 p0 p6 p3 : Prop)
theorem file61_107430 : (((((p2 ∨ p4) → False) → ((p4 → False) ∨ (p1 ∨ True))) → False) → ((((p4 ∨ p5) → False) ∧ ((p7 → False) ∧ (p0 ∨ p1))) ∨ (((p1 ∨ p3) → (p6 ∨ p1)) → ((True → False) ∧ (p6 ∨ False))))) := by
  intro assump_1
  apply Or.inr
  intro assump_62
  apply And.intro
  intro assump_63
  have assump_102 : (((p2 ∨ p4) → False) → ((p4 → False) ∨ (p1 ∨ True))) := by
    intro assump_70
    apply Or.inl
    intro assump_73
    have assump_103 : (p2 ∨ p4) := by
      apply Or.inr
      exact assump_73
    let assump_77 := assump_70 assump_103
    apply False.elim assump_77
  let assump_69 := assump_1 assump_102
  apply False.elim assump_69
  have assump_104 : (((p2 ∨ p4) → False) → ((p4 → False) ∨ (p1 ∨ True))) := by
    intro assump_88
    apply Or.inl
    intro assump_91
    have assump_105 : (p2 ∨ p4) := by
      apply Or.inr
      exact assump_91
    let assump_95 := assump_88 assump_105
    apply False.elim assump_95
  let assump_87 := assump_1 assump_104
  apply False.elim assump_87


variable (p1 p2 p6 : Prop)
theorem file61_108467 : (((((p1 ∨ p2) ∨ (False → p6)) → False) → False) ∨ ((((p6 → False) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p1 ∨ p2) ∨ (False → p6)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p3 p1 p2 p7 p0 p5 p6 : Prop)
theorem file61_108848 : (((((p4 ∨ p0) ∨ (p0 → p6)) ∨ ((p0 → False) ∨ (p5 ∨ p5))) → False) → ((((p2 ∧ p3) → (p3 ∨ p2)) → ((p0 → False) ∨ (p2 → p6))) ∨ (((p4 ∨ p1) ∧ (p2 ∨ p7)) → ((p0 ∨ p6) ∨ (p7 → p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  have assump_16 : (((p4 ∨ p0) ∨ (p0 → p6)) ∨ ((p0 → False) ∨ (p5 ∨ p5))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    exact assump_7
  let assump_12 := assump_1 assump_16
  apply False.elim assump_12


variable (p2 p4 p7 p0 p6 p5 p1 : Prop)
theorem file61_109395 : ((((((p5 → False) ∧ (p1 → p6)) → ((p7 ∧ p2) → (p0 → True))) ∨ (((p7 ∧ True) ∧ (p2 → p4)) ∨ ((False ∧ True) → (True → False)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 → False) ∧ (p1 → p6)) → ((p7 ∧ p2) → (p0 → True))) ∨ (((p7 ∧ True) ∧ (p2 → p4)) ∨ ((False ∧ True) → (True → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p0 p7 p6 p2 p4 : Prop)
theorem file61_109933 : ((((((True → False) ∨ (p1 ∧ p0)) ∧ ((p7 ∨ p6) ∨ (p1 → False))) → (((p2 → False) ∧ (p0 → False)) → ((p6 ∧ p2) → (p6 ∧ p4)))) → False) → False) := by
  intro assump_7
  have assump_138 : ((((True → False) ∨ (p1 ∧ p0)) ∧ ((p7 ∨ p6) ∨ (p1 → False))) → (((p2 → False) ∧ (p0 → False)) → ((p6 ∧ p2) → (p6 ∧ p4)))) := by
    intro assump_11
    intro assump_12
    intro assump_13
    apply And.intro
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_12
      case intro assump_20 assump_21 =>
        cases assump_11
        case intro assump_26 assump_27 =>
          cases assump_26
          case inl assump_28 =>
            cases assump_27
            case inl assump_32 =>
              cases assump_32
              case inl assump_34 =>
                exact assump_14
              case inr assump_35 =>
                exact assump_35
            case inr assump_33 =>
              exact assump_14
          case inr assump_29 =>
            cases assump_29
            case intro assump_42 assump_43 =>
              cases assump_27
              case inl assump_48 =>
                cases assump_48
                case inl assump_50 =>
                  exact assump_14
                case inr assump_51 =>
                  exact assump_51
              case inr assump_49 =>
                exact assump_14
    cases assump_13
    case intro assump_58 assump_59 =>
      cases assump_12
      case intro assump_64 assump_65 =>
        cases assump_11
        case intro assump_70 assump_71 =>
          cases assump_70
          case inl assump_72 =>
            cases assump_71
            case inl assump_76 =>
              cases assump_76
              case inl assump_78 =>
                have assump_139 : True := by
                  apply True.intro
                let assump_83 := assump_72 assump_139
                apply False.elim assump_83
              case inr assump_79 =>
                have assump_140 : True := by
                  apply True.intro
                let assump_90 := assump_72 assump_140
                apply False.elim assump_90
            case inr assump_77 =>
              have assump_141 : True := by
                apply True.intro
              let assump_97 := assump_72 assump_141
              apply False.elim assump_97
          case inr assump_73 =>
            cases assump_73
            case intro assump_101 assump_102 =>
              cases assump_71
              case inl assump_107 =>
                cases assump_107
                case inl assump_109 =>
                  have assump_142 : p0 := by
                    exact assump_102
                  let assump_116 := assump_65 assump_142
                  apply False.elim assump_116
                case inr assump_110 =>
                  have assump_143 : p0 := by
                    exact assump_102
                  let assump_125 := assump_65 assump_143
                  apply False.elim assump_125
              case inr assump_108 =>
                have assump_144 : p1 := by
                  exact assump_101
                let assump_131 := assump_108 assump_144
                apply False.elim assump_131
  let assump_10 := assump_7 assump_138
  apply False.elim assump_10


variable (p5 p2 p3 p4 p6 : Prop)
theorem file61_113239 : ((((((p4 → False) ∧ (p5 ∨ p5)) → ((p2 ∧ p5) → (False → p4))) ∨ (((p6 → False) → (p3 → p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p4 → False) ∧ (p5 ∨ p5)) → ((p2 ∧ p5) → (False → p4))) ∨ (((p6 → False) → (p3 → p3)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p0 p3 p5 p7 p6 p4 : Prop)
theorem file61_113734 : (((((p0 → p6) → (p4 ∨ p4)) → False) → False) → ((((False ∧ p5) ∧ (True → False)) → False) ∨ (((p7 → p3) ∨ (p5 ∧ True)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_7


variable (p2 p1 p6 p7 p5 : Prop)
theorem file61_114114 : ((((((True → p7) → (p5 ∨ p6)) ∨ ((p7 → False) → (p2 ∧ p7))) → (((p5 ∧ False) → (p6 → False)) ∨ ((True → p1) → False))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((True → p7) → (p5 ∨ p6)) ∨ ((p7 → False) → (p2 ∧ p7))) → (((p5 ∧ False) → (p6 → False)) ∨ ((True → p1) → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
    case inr assump_7 =>
      apply Or.inl
      intro assump_22
      intro assump_23
      cases assump_22
      case intro assump_26 assump_27 =>
        apply False.elim assump_27
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p6 p2 p4 p0 p7 p5 p1 p3 : Prop)
theorem file61_114955 : ((((((p2 ∧ p3) ∨ (p7 → False)) → ((False ∧ False) → (p4 ∨ p6))) → False) ∧ ((((p3 ∨ p5) ∨ (p7 ∧ p4)) → False) ∨ (((p1 → False) ∨ (False → p2)) ∨ ((p0 ∨ p0) ∨ (p3 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_94 : (((p2 ∧ p3) ∨ (p7 → False)) → ((False ∧ False) → (p4 ∨ p6))) := by
        intro assump_12
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
      let assump_11 := assump_2 assump_94
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case inl assump_21 =>
        cases assump_21
        case inl assump_23 =>
          have assump_95 : (((p2 ∧ p3) ∨ (p7 → False)) → ((False ∧ False) → (p4 ∨ p6))) := by
            intro assump_29
            intro assump_30
            cases assump_30
            case intro assump_31 assump_32 =>
              apply False.elim assump_31
          let assump_28 := assump_2 assump_95
          apply False.elim assump_28
        case inr assump_24 =>
          have assump_96 : (((p2 ∧ p3) ∨ (p7 → False)) → ((False ∧ False) → (p4 ∨ p6))) := by
            intro assump_42
            intro assump_43
            cases assump_43
            case intro assump_44 assump_45 =>
              apply False.elim assump_44
          let assump_41 := assump_2 assump_96
          apply False.elim assump_41
      case inr assump_22 =>
        cases assump_22
        case inl assump_51 =>
          cases assump_51
          case inl assump_53 =>
            have assump_97 : (((p2 ∧ p3) ∨ (p7 → False)) → ((False ∧ False) → (p4 ∨ p6))) := by
              intro assump_59
              intro assump_60
              cases assump_60
              case intro assump_61 assump_62 =>
                apply False.elim assump_61
            let assump_58 := assump_2 assump_97
            apply False.elim assump_58
          case inr assump_54 =>
            have assump_98 : (((p2 ∧ p3) ∨ (p7 → False)) → ((False ∧ False) → (p4 ∨ p6))) := by
              intro assump_72
              intro assump_73
              cases assump_73
              case intro assump_74 assump_75 =>
                apply False.elim assump_74
            let assump_71 := assump_2 assump_98
            apply False.elim assump_71
        case inr assump_52 =>
          have assump_99 : (((p2 ∧ p3) ∨ (p7 → False)) → ((False ∧ False) → (p4 ∨ p6))) := by
            intro assump_85
            intro assump_86
            cases assump_86
            case intro assump_87 assump_88 =>
              apply False.elim assump_87
          let assump_84 := assump_2 assump_99
          apply False.elim assump_84


variable (p0 p1 p5 p7 p3 p6 p4 : Prop)
theorem file61_117768 : (((((True → False) → (p4 ∧ p4)) ∧ ((p1 ∧ p7) ∧ (p1 → p6))) ∧ (((p6 ∨ p0) → False) ∧ ((p1 → True) → (p1 → False)))) → ((((p0 ∨ p0) → (True ∨ False)) → ((p3 ∧ p3) → (p0 ∧ p5))) ∧ (((p3 → p7) → (False ∧ p7)) → ((True ∧ True) ∧ (p7 ∧ p6))))) := by
  intro assump_13
  apply And.intro
  intro assump_14
  intro assump_15
  apply And.intro
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_13
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_27
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            cases assump_25
            case intro assump_40 assump_41 =>
              have assump_143 : (p1 → True) := by
                intro assump_47
                apply True.intro
              let assump_46 := assump_41 assump_143
              have assump_144 : p1 := by
                exact assump_32
              let assump_48 := assump_46 assump_144
              apply False.elim assump_48
  cases assump_15
  case intro assump_52 assump_53 =>
    cases assump_13
    case intro assump_60 assump_61 =>
      cases assump_60
      case intro assump_62 assump_63 =>
        cases assump_63
        case intro assump_66 assump_67 =>
          cases assump_66
          case intro assump_68 assump_69 =>
            cases assump_61
            case intro assump_76 assump_77 =>
              have assump_145 : (p1 → True) := by
                intro assump_83
                apply True.intro
              let assump_82 := assump_77 assump_145
              have assump_146 : p1 := by
                exact assump_68
              let assump_84 := assump_82 assump_146
              apply False.elim assump_84
  intro assump_88
  apply And.intro
  apply And.intro
  apply True.intro
  apply True.intro
  apply And.intro
  cases assump_13
  case intro assump_91 assump_92 =>
    cases assump_91
    case intro assump_93 assump_94 =>
      cases assump_94
      case intro assump_97 assump_98 =>
        cases assump_97
        case intro assump_99 assump_100 =>
          cases assump_92
          case intro assump_107 assump_108 =>
            exact assump_100
  cases assump_13
  case intro assump_115 assump_116 =>
    cases assump_115
    case intro assump_117 assump_118 =>
      cases assump_118
      case intro assump_121 assump_122 =>
        cases assump_121
        case intro assump_123 assump_124 =>
          cases assump_116
          case intro assump_131 assump_132 =>
            have assump_147 : (p1 → True) := by
              intro assump_138
              apply True.intro
            let assump_137 := assump_132 assump_147
            have assump_148 : p1 := by
              exact assump_123
            let assump_139 := assump_137 assump_148
            apply False.elim assump_139


