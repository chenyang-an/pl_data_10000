variable (p4 p0 p6 p7 p5 p2 : Prop)
theorem file12_44 : (((((p7 ∧ p0) ∧ (p6 → p4)) ∧ ((p0 → False) → (p4 ∨ p0))) ∧ (((p5 → False) → (p0 ∨ p6)) → False)) → ((((p0 → False) ∧ (p2 → False)) ∨ ((p6 → False) → (True ∨ True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_15
            case intro assump_17 assump_18 =>
              have assump_63 : ((p5 → False) → (p0 ∨ p6)) := by
                intro assump_30
                apply Or.inl
                exact assump_18
              let assump_29 := assump_12 assump_63
              apply False.elim assump_29
  case inr assump_4 =>
    cases assump_1
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            have assump_64 : ((p5 → False) → (p0 ∨ p6)) := by
              intro assump_57
              apply Or.inl
              exact assump_45
            let assump_56 := assump_39 assump_64
            apply False.elim assump_56


variable (p5 p7 p4 p6 p3 p1 p2 : Prop)
theorem file12_1452 : ((((((p5 → p1) → (False → False)) ∧ ((False ∧ p6) → (p3 ∨ p2))) ∨ (((False → False) → (p4 ∧ p5)) ∧ ((p1 → False) ∧ (p7 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p5 → p1) → (False → False)) ∧ ((False ∧ p6) → (p3 ∨ p2))) ∨ (((False → False) → (p4 ∧ p5)) ∧ ((p1 → False) ∧ (p7 ∨ p5)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p6 p3 p1 p0 p7 p5 p4 p2 : Prop)
theorem file12_2117 : ((((((p5 ∨ p4) ∧ (p3 ∨ True)) → ((False → p6) → False)) → (((p6 ∧ p6) ∨ (p1 ∧ p5)) → ((p2 → p6) ∨ (p7 → p2)))) ∧ ((((p0 ∧ p0) ∨ (True → False)) ∨ ((True ∧ p6) → False)) ∧ (((p4 ∧ False) → (p0 → p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_70 : ((p4 ∧ False) → (p0 → p6)) := by
              intro assump_21
              intro assump_22
              cases assump_21
              case intro assump_25 assump_26 =>
                apply False.elim assump_26
            let assump_20 := assump_7 assump_70
            apply False.elim assump_20
        case inr assump_11 =>
          have assump_71 : ((p4 ∧ False) → (p0 → p6)) := by
            intro assump_39
            intro assump_40
            cases assump_39
            case intro assump_43 assump_44 =>
              apply False.elim assump_44
          let assump_38 := assump_7 assump_71
          apply False.elim assump_38
      case inr assump_9 =>
        have assump_72 : ((p4 ∧ False) → (p0 → p6)) := by
          intro assump_57
          intro assump_58
          cases assump_57
          case intro assump_61 assump_62 =>
            apply False.elim assump_62
        let assump_56 := assump_7 assump_72
        apply False.elim assump_56


variable (p4 p3 p7 p1 p5 p6 : Prop)
theorem file12_3695 : ((((((False ∨ False) ∨ (p4 → False)) ∧ ((True ∨ p6) → False)) ∧ (((p7 → p5) → False) → ((p3 ∨ p3) → False))) ∧ ((((p6 → p1) → False) → False) ∧ (((True ∨ True) → False) ∨ ((True → False) ∧ (p1 ∨ True))))) → False) := by
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
            apply False.elim assump_10
          case inr assump_11 =>
            apply False.elim assump_11
        case inr assump_9 =>
          cases assump_3
          case intro assump_22 assump_23 =>
            cases assump_23
            case inl assump_26 =>
              have assump_53 : (True ∨ True) := by
                apply Or.inl
                apply True.intro
              let assump_30 := assump_26 assump_53
              apply False.elim assump_30
            case inr assump_27 =>
              cases assump_27
              case intro assump_34 assump_35 =>
                cases assump_35
                case inl assump_38 =>
                  have assump_54 : True := by
                    apply True.intro
                  let assump_43 := assump_34 assump_54
                  apply False.elim assump_43
                case inr assump_39 =>
                  have assump_55 : True := by
                    apply True.intro
                  let assump_49 := assump_34 assump_55
                  apply False.elim assump_49


variable (p7 p3 p2 p1 p0 p4 p5 p6 : Prop)
theorem file12_5333 : ((((((p7 → p1) → (p4 ∧ False)) → ((False ∨ p7) → (p0 ∨ False))) ∨ (((True → True) ∨ (p0 → p7)) ∨ ((p3 → False) → (False → p7)))) ∧ ((((p0 → False) ∧ (p4 ∧ p5)) → ((p4 ∧ p1) → (p2 → False))) ∧ (((False ∧ p3) ∨ (True ∨ p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_58 : ((False ∧ p3) ∨ (True ∨ p6)) := by
          apply Or.inr
          apply Or.inl
          apply True.intro
        let assump_14 := assump_9 assump_58
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case inl assump_18 =>
        cases assump_18
        case inl assump_20 =>
          cases assump_3
          case intro assump_24 assump_25 =>
            have assump_59 : ((False ∧ p3) ∨ (True ∨ p6)) := by
              apply Or.inr
              apply Or.inl
              apply True.intro
            let assump_30 := assump_25 assump_59
            apply False.elim assump_30
        case inr assump_21 =>
          cases assump_3
          case intro assump_36 assump_37 =>
            have assump_60 : ((False ∧ p3) ∨ (True ∨ p6)) := by
              apply Or.inr
              apply Or.inl
              apply True.intro
            let assump_42 := assump_37 assump_60
            apply False.elim assump_42
      case inr assump_19 =>
        cases assump_3
        case intro assump_48 assump_49 =>
          have assump_61 : ((False ∧ p3) ∨ (True ∨ p6)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_54 := assump_49 assump_61
          apply False.elim assump_54


variable (p6 p2 p7 p4 p3 p1 p5 : Prop)
theorem file12_7115 : (((((p3 ∨ p2) ∧ (True → False)) → ((p5 → False) → False)) ∧ (((False ∨ True) ∨ (p2 → True)) → ((p4 ∧ p1) ∧ (p3 ∧ False)))) → ((((p7 ∧ p3) ∨ (p3 ∨ p3)) ∨ ((p4 ∨ p6) ∧ (p1 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case intro assump_13 assump_14 =>
          have assump_111 : ((False ∨ True) ∨ (p2 → True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_19 := assump_14 assump_111
          let assump_20 := And.right assump_19
          let assump_24 := And.right assump_20
          apply False.elim assump_24
    case inr assump_6 =>
      cases assump_6
      case inl assump_29 =>
        cases assump_1
        case intro assump_33 assump_34 =>
          have assump_112 : ((False ∨ True) ∨ (p2 → True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_39 := assump_34 assump_112
          let assump_40 := And.right assump_39
          let assump_44 := And.right assump_40
          apply False.elim assump_44
      case inr assump_30 =>
        cases assump_1
        case intro assump_51 assump_52 =>
          have assump_113 : ((False ∨ True) ∨ (p2 → True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_57 := assump_52 assump_113
          let assump_58 := And.right assump_57
          let assump_62 := And.right assump_58
          apply False.elim assump_62
  case inr assump_4 =>
    cases assump_4
    case intro assump_67 assump_68 =>
      cases assump_67
      case inl assump_69 =>
        cases assump_1
        case intro assump_75 assump_76 =>
          have assump_114 : ((False ∨ True) ∨ (p2 → True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_81 := assump_76 assump_114
          let assump_82 := And.right assump_81
          let assump_86 := And.right assump_82
          apply False.elim assump_86
      case inr assump_70 =>
        cases assump_1
        case intro assump_95 assump_96 =>
          have assump_115 : ((False ∨ True) ∨ (p2 → True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_101 := assump_96 assump_115
          let assump_102 := And.right assump_101
          let assump_106 := And.right assump_102
          apply False.elim assump_106


variable (p4 p3 p7 p1 p5 p2 p6 : Prop)
theorem file12_9758 : (((((p7 ∨ True) → False) ∧ ((p7 → True) ∧ (False ∨ p2))) → (((p3 ∨ p2) ∨ (False → p6)) ∨ ((p6 → False) ∨ (p6 ∨ p7)))) ∨ ((((p5 ∧ p4) → False) → False) ∨ (((p2 ∧ p1) → False) ∧ ((p2 ∧ p3) → (p4 → p4))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply False.elim assump_10
      case inr assump_11 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        exact assump_11


variable (p5 p6 p2 p1 p4 p0 p3 : Prop)
theorem file12_10367 : ((((((p4 → False) ∨ (p5 → False)) → False) → (((p0 → False) → False) ∨ ((p1 ∧ p4) ∨ (p0 ∨ p2)))) ∧ ((((p0 ∧ p3) ∧ (p4 → False)) → ((True → False) → (True ∧ p5))) → (((p6 ∨ True) ∨ (p3 → p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_34 : (((p0 ∧ p3) ∧ (p4 → False)) → ((True → False) → (True ∧ p5))) := by
      intro assump_9
      intro assump_10
      apply And.intro
      apply True.intro
      cases assump_9
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          have assump_35 : True := by
            apply True.intro
          let assump_26 := assump_10 assump_35
          apply False.elim assump_26
    let assump_8 := assump_3 assump_34
    have assump_36 : ((p6 ∨ True) ∨ (p3 → p3)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_30 := assump_8 assump_36
    apply False.elim assump_30


variable (p6 p5 p0 p1 p2 : Prop)
theorem file12_11388 : ((((((p2 → p1) ∧ (p5 ∧ p0)) → False) → (((False ∨ p5) ∨ (p6 ∨ True)) ∨ ((False → False) ∧ (False ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p2 → p1) ∧ (p5 ∧ p0)) → False) → (((False ∨ p5) ∨ (p6 ∨ True)) ∨ ((False → False) ∧ (False ∧ p5)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p4 p0 : Prop)
theorem file12_11871 : (((((False ∧ p3) ∧ (p4 ∨ p0)) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((False ∧ p3) ∧ (p4 ∨ p0)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p1 p0 p5 p6 : Prop)
theorem file12_12302 : (((((p1 → False) ∧ (True → False)) → ((p0 ∧ p5) ∧ (True ∧ p2))) ∨ (((False → False) → (True → p0)) → ((p5 ∨ p5) ∨ (False → False)))) ∨ ((((p0 ∨ p2) → (True ∧ p1)) → False) ∧ (((p0 → False) → (p6 ∨ p5)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_32 : True := by
      apply True.intro
    let assump_8 := assump_3 assump_32
    apply False.elim assump_8
  cases assump_1
  case intro assump_12 assump_13 =>
    have assump_33 : True := by
      apply True.intro
    let assump_18 := assump_13 assump_33
    apply False.elim assump_18
  apply And.intro
  apply True.intro
  cases assump_1
  case intro assump_22 assump_23 =>
    have assump_34 : True := by
      apply True.intro
    let assump_28 := assump_23 assump_34
    apply False.elim assump_28


variable (p2 p0 p3 p6 p4 p7 p1 : Prop)
theorem file12_13239 : (((((p1 ∨ False) ∨ (p0 → True)) ∨ ((p7 ∨ p7) ∨ (False → False))) → (((p3 → p1) ∧ (False ∧ p6)) → ((p7 ∧ p3) → (p2 ∧ p3)))) ∨ ((((p4 → False) ∨ (p1 ∨ p7)) → False) → (((p4 → True) → False) → ((p3 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
  cases assump_3
  case intro assump_18 assump_19 =>
    cases assump_2
    case intro assump_24 assump_25 =>
      cases assump_25
      case intro assump_28 assump_29 =>
        apply False.elim assump_28


variable (p1 p5 p7 p4 : Prop)
theorem file12_14011 : (((((p4 ∧ p1) ∧ (p5 → False)) → ((p4 ∧ p7) → (True → True))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p4 ∧ p1) ∧ (p5 → False)) → ((p4 ∧ p7) → (True → True))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p6 p4 p1 p7 : Prop)
theorem file12_14397 : ((((((p1 ∧ p4) ∧ (p6 → True)) ∨ ((True ∨ p1) ∧ (p4 → False))) → (((p4 ∧ True) ∧ (p4 → False)) → False)) → ((((p7 ∨ False) → (p0 ∨ p7)) ∧ ((p7 → p7) → False)) ∧ (((p6 → True) → (p1 ∧ p7)) → False))) → False) := by
  intro assump_1
  have assump_66 : ((((p1 ∧ p4) ∧ (p6 → True)) ∨ ((True ∨ p1) ∧ (p4 → False))) → (((p4 ∧ True) ∧ (p4 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_5
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              have assump_67 : p4 := by
                exact assump_22
              let assump_32 := assump_8 assump_67
              apply False.elim assump_32
        case inr assump_18 =>
          cases assump_18
          case intro assump_36 assump_37 =>
            cases assump_36
            case inl assump_38 =>
              have assump_68 : p4 := by
                exact assump_9
              let assump_44 := assump_37 assump_68
              apply False.elim assump_44
            case inr assump_39 =>
              have assump_69 : p4 := by
                exact assump_9
              let assump_52 := assump_37 assump_69
              apply False.elim assump_52
  let assump_4 := assump_1 assump_66
  let assump_56 := And.left assump_4
  let assump_57 := And.right assump_56
  have assump_70 : (p7 → p7) := by
    intro assump_60
    exact assump_60
  let assump_59 := assump_57 assump_70
  apply False.elim assump_59


variable (p3 p5 p6 p2 p0 p7 p4 : Prop)
theorem file12_16108 : (((((p5 ∨ p4) ∨ (False ∧ p0)) → False) ∨ (((p4 ∧ p7) ∨ (p4 → False)) ∨ ((p3 ∧ p6) ∧ (p7 → False)))) → ((((p4 ∨ p5) → (p0 ∨ p5)) → ((p0 → p4) → False)) → (((p5 ∨ p0) ∨ (p2 ∧ p2)) ∨ ((p0 ∧ p4) → (p5 → False))))) := by
  intro assump_5
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    apply Or.inr
    intro assump_13
    intro assump_14
    cases assump_13
    case intro assump_17 assump_18 =>
      have assump_130 : ((p5 ∨ p4) ∨ (False ∧ p0)) := by
        apply Or.inl
        apply Or.inl
        exact assump_14
      let assump_26 := assump_9 assump_130
      apply False.elim assump_26
  case inr assump_10 =>
    cases assump_10
    case inl assump_30 =>
      cases assump_30
      case inl assump_32 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          apply Or.inr
          intro assump_40
          intro assump_41
          cases assump_40
          case intro assump_44 assump_45 =>
            have assump_131 : ((p4 ∨ p5) → (p0 ∨ p5)) := by
              intro assump_56
              cases assump_56
              case inl assump_57 =>
                apply Or.inl
                exact assump_44
              case inr assump_58 =>
                apply Or.inl
                exact assump_44
            let assump_55 := assump_6 assump_131
            have assump_132 : (p0 → p4) := by
              intro assump_64
              exact assump_45
            let assump_63 := assump_55 assump_132
            apply False.elim assump_63
      case inr assump_33 =>
        apply Or.inr
        intro assump_72
        intro assump_73
        cases assump_72
        case intro assump_76 assump_77 =>
          have assump_133 : p4 := by
            exact assump_77
          let assump_85 := assump_33 assump_133
          apply False.elim assump_85
    case inr assump_31 =>
      cases assump_31
      case intro assump_89 assump_90 =>
        cases assump_89
        case intro assump_91 assump_92 =>
          apply Or.inr
          intro assump_99
          intro assump_100
          cases assump_99
          case intro assump_103 assump_104 =>
            have assump_134 : ((p4 ∨ p5) → (p0 ∨ p5)) := by
              intro assump_116
              cases assump_116
              case inl assump_117 =>
                apply Or.inl
                exact assump_103
              case inr assump_118 =>
                apply Or.inl
                exact assump_103
            let assump_115 := assump_6 assump_134
            have assump_135 : (p0 → p4) := by
              intro assump_124
              exact assump_104
            let assump_123 := assump_115 assump_135
            apply False.elim assump_123


variable (p4 p1 p7 p2 p5 p6 : Prop)
theorem file12_18846 : (((((False → False) ∨ (p4 ∨ p2)) ∨ ((p2 ∨ p6) → (p1 → p4))) → False) → ((((False ∧ p7) ∧ (p6 → p5)) ∨ ((p4 → p6) → False)) → False)) := by
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
    have assump_22 : (((False → False) ∨ (p4 ∨ p2)) ∨ ((p2 ∨ p6) → (p1 → p4))) := by
      apply Or.inl
      apply Or.inl
      intro assump_16
      apply False.elim assump_16
    let assump_15 := assump_1 assump_22
    apply False.elim assump_15


variable (p4 p1 p3 : Prop)
theorem file12_19530 : (((((p3 → False) → False) → False) ∧ (((p4 → True) → False) ∨ ((p1 → p1) → False))) → ((((True → False) → False) ∨ ((p4 → False) → (p4 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        have assump_53 : (p4 → True) := by
          intro assump_16
          apply True.intro
        let assump_15 := assump_11 assump_53
        apply False.elim assump_15
      case inr assump_12 =>
        have assump_54 : (p1 → p1) := by
          intro assump_23
          exact assump_23
        let assump_22 := assump_12 assump_54
        apply False.elim assump_22
  case inr assump_4 =>
    cases assump_1
    case intro assump_31 assump_32 =>
      cases assump_32
      case inl assump_35 =>
        have assump_55 : (p4 → True) := by
          intro assump_40
          apply True.intro
        let assump_39 := assump_35 assump_55
        apply False.elim assump_39
      case inr assump_36 =>
        have assump_56 : (p1 → p1) := by
          intro assump_47
          exact assump_47
        let assump_46 := assump_36 assump_56
        apply False.elim assump_46


variable (p5 p4 p0 p1 : Prop)
theorem file12_20808 : (((((p5 ∨ p0) ∨ (p1 → False)) → ((False ∧ p4) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : (((p5 ∨ p0) ∨ (p1 → False)) → ((False ∧ p4) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p1 p4 p0 p5 p2 : Prop)
theorem file12_21234 : (((((p5 ∧ p2) → (p2 ∧ p1)) ∨ ((p6 → p2) → False)) ∧ (((True → False) ∧ (p6 → False)) ∧ ((True → False) ∨ (False → False)))) → ((((True → p4) ∧ (False → False)) ∧ ((True ∧ p6) ∧ (p4 → False))) ∧ (((p5 ∨ p4) ∨ (False → False)) ∨ ((True → p0) → (p0 → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case inl assump_19 =>
            have assump_227 : True := by
              apply True.intro
            let assump_23 := assump_19 assump_227
            apply False.elim assump_23
          case inr assump_20 =>
            have assump_228 : True := by
              apply True.intro
            let assump_31 := assump_13 assump_228
            apply False.elim assump_31
    case inr assump_8 =>
      cases assump_6
      case intro assump_37 assump_38 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          cases assump_38
          case inl assump_45 =>
            have assump_229 : True := by
              apply True.intro
            let assump_49 := assump_45 assump_229
            apply False.elim assump_49
          case inr assump_46 =>
            have assump_230 : True := by
              apply True.intro
            let assump_57 := assump_39 assump_230
            apply False.elim assump_57
  intro assump_61
  apply False.elim assump_61
  apply And.intro
  apply And.intro
  apply True.intro
  cases assump_1
  case intro assump_64 assump_65 =>
    cases assump_64
    case inl assump_66 =>
      cases assump_65
      case intro assump_70 assump_71 =>
        cases assump_70
        case intro assump_72 assump_73 =>
          cases assump_71
          case inl assump_78 =>
            have assump_231 : True := by
              apply True.intro
            let assump_82 := assump_78 assump_231
            apply False.elim assump_82
          case inr assump_79 =>
            have assump_232 : True := by
              apply True.intro
            let assump_90 := assump_72 assump_232
            apply False.elim assump_90
    case inr assump_67 =>
      cases assump_65
      case intro assump_96 assump_97 =>
        cases assump_96
        case intro assump_98 assump_99 =>
          cases assump_97
          case inl assump_104 =>
            have assump_233 : True := by
              apply True.intro
            let assump_108 := assump_104 assump_233
            apply False.elim assump_108
          case inr assump_105 =>
            have assump_234 : True := by
              apply True.intro
            let assump_116 := assump_98 assump_234
            apply False.elim assump_116
  intro assump_120
  cases assump_1
  case intro assump_123 assump_124 =>
    cases assump_123
    case inl assump_125 =>
      cases assump_124
      case intro assump_129 assump_130 =>
        cases assump_129
        case intro assump_131 assump_132 =>
          cases assump_130
          case inl assump_137 =>
            have assump_235 : True := by
              apply True.intro
            let assump_141 := assump_137 assump_235
            apply False.elim assump_141
          case inr assump_138 =>
            have assump_236 : True := by
              apply True.intro
            let assump_149 := assump_131 assump_236
            apply False.elim assump_149
    case inr assump_126 =>
      cases assump_124
      case intro assump_155 assump_156 =>
        cases assump_155
        case intro assump_157 assump_158 =>
          cases assump_156
          case inl assump_163 =>
            have assump_237 : True := by
              apply True.intro
            let assump_167 := assump_163 assump_237
            apply False.elim assump_167
          case inr assump_164 =>
            have assump_238 : True := by
              apply True.intro
            let assump_175 := assump_157 assump_238
            apply False.elim assump_175
  cases assump_1
  case intro assump_179 assump_180 =>
    cases assump_179
    case inl assump_181 =>
      cases assump_180
      case intro assump_185 assump_186 =>
        cases assump_185
        case intro assump_187 assump_188 =>
          cases assump_186
          case inl assump_193 =>
            apply Or.inl
            apply Or.inr
            intro assump_197
            apply False.elim assump_197
          case inr assump_194 =>
            apply Or.inl
            apply Or.inr
            intro assump_202
            apply False.elim assump_202
    case inr assump_182 =>
      cases assump_180
      case intro assump_207 assump_208 =>
        cases assump_207
        case intro assump_209 assump_210 =>
          cases assump_208
          case inl assump_215 =>
            apply Or.inl
            apply Or.inr
            intro assump_219
            apply False.elim assump_219
          case inr assump_216 =>
            apply Or.inl
            apply Or.inr
            intro assump_224
            apply False.elim assump_224


variable (p3 p7 p0 p4 p2 : Prop)
theorem file12_26475 : ((((((p4 → False) → (False → p0)) ∨ ((p2 ∧ True) → False)) ∨ (((p4 → False) → False) ∨ ((p3 ∧ p7) ∨ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p4 → False) → (False → p0)) ∨ ((p2 ∧ True) → False)) ∨ (((p4 → False) → False) ∨ ((p3 ∧ p7) ∨ (p2 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p6 p2 p0 p1 p7 p3 : Prop)
theorem file12_27001 : (((((p6 → p2) ∧ (True ∨ p1)) ∧ ((p5 → p7) → False)) → (((p7 → p1) ∧ (p0 ∨ False)) → ((p0 ∨ p6) ∧ (p6 → p6)))) ∨ ((((p3 ∧ p3) → (p1 ∨ p5)) ∧ ((p1 ∧ p6) → False)) ∧ (((p0 ∧ p3) ∨ (p5 → False)) → ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_14
          case inl assump_17 =>
            apply Or.inl
            exact assump_7
          case inr assump_18 =>
            apply Or.inl
            exact assump_7
    case inr assump_8 =>
      apply False.elim assump_8
  intro assump_29
  cases assump_2
  case intro assump_32 assump_33 =>
    cases assump_33
    case inl assump_36 =>
      cases assump_1
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          cases assump_43
          case inl assump_46 =>
            exact assump_29
          case inr assump_47 =>
            exact assump_29
    case inr assump_37 =>
      apply False.elim assump_37


variable (p1 p6 p2 p7 : Prop)
theorem file12_28269 : (((((p7 → False) → (p6 → p2)) → ((p1 → False) → False)) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((True → False) → False) := by
      intro assump_9
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p4 p5 p2 p1 p3 p0 p7 p6 : Prop)
theorem file12_28788 : (((((True → False) ∧ (p0 → False)) ∧ ((p1 ∨ p2) ∨ (p2 → False))) → (((p7 ∧ p5) → (p5 ∧ p2)) → ((p6 → p6) → (p3 → p6)))) ∨ ((((p1 → False) → (p4 → True)) → ((p2 → False) → False)) ∧ (((p6 ∨ p6) → (p0 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_1
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_12
      case inl assump_19 =>
        cases assump_19
        case inl assump_21 =>
          have assump_47 : True := by
            apply True.intro
          let assump_27 := assump_13 assump_47
          apply False.elim assump_27
        case inr assump_22 =>
          have assump_48 : True := by
            apply True.intro
          let assump_35 := assump_13 assump_48
          apply False.elim assump_35
      case inr assump_20 =>
        have assump_49 : True := by
          apply True.intro
        let assump_43 := assump_13 assump_49
        apply False.elim assump_43


variable (p4 p0 p1 p7 : Prop)
theorem file12_29869 : ((((((p0 → p7) → (False ∧ p1)) → False) → (((p4 ∧ True) → (p7 → False)) → ((p0 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p0 → p7) → (False ∧ p1)) → False) → (((p4 ∧ True) → (p7 → False)) → ((p0 ∧ False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p6 p2 p4 p1 p5 p0 p3 : Prop)
theorem file12_30406 : ((((((p3 ∧ p4) ∧ (p7 ∧ p3)) → ((p5 ∧ p3) → False)) ∧ (((p6 → p0) → (False → False)) → False)) ∧ ((((p6 ∧ p0) → False) ∨ ((p7 ∧ p2) ∧ (p0 ∧ True))) ∨ (((p2 → False) ∧ (False → p1)) ∨ ((p5 ∧ p0) ∨ (p4 ∨ p5))))) → False) := by
  intro assump_27
  cases assump_27
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      cases assump_29
      case inl assump_36 =>
        cases assump_36
        case inl assump_38 =>
          have assump_136 : ((p6 → p0) → (False → False)) := by
            intro assump_44
            intro assump_45
            apply False.elim assump_45
          let assump_43 := assump_31 assump_136
          apply False.elim assump_43
        case inr assump_39 =>
          cases assump_39
          case intro assump_51 assump_52 =>
            cases assump_51
            case intro assump_53 assump_54 =>
              cases assump_52
              case intro assump_59 assump_60 =>
                have assump_137 : ((p6 → p0) → (False → False)) := by
                  intro assump_69
                  intro assump_70
                  apply False.elim assump_70
                let assump_68 := assump_31 assump_137
                apply False.elim assump_68
      case inr assump_37 =>
        cases assump_37
        case inl assump_76 =>
          cases assump_76
          case intro assump_78 assump_79 =>
            have assump_138 : ((p6 → p0) → (False → False)) := by
              intro assump_87
              intro assump_88
              apply False.elim assump_88
            let assump_86 := assump_31 assump_138
            apply False.elim assump_86
        case inr assump_77 =>
          cases assump_77
          case inl assump_94 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              have assump_139 : ((p6 → p0) → (False → False)) := by
                intro assump_105
                intro assump_106
                apply False.elim assump_106
              let assump_104 := assump_31 assump_139
              apply False.elim assump_104
          case inr assump_95 =>
            cases assump_95
            case inl assump_112 =>
              have assump_140 : ((p6 → p0) → (False → False)) := by
                intro assump_118
                intro assump_119
                apply False.elim assump_119
              let assump_117 := assump_31 assump_140
              apply False.elim assump_117
            case inr assump_113 =>
              have assump_141 : ((p6 → p0) → (False → False)) := by
                intro assump_129
                intro assump_130
                apply False.elim assump_130
              let assump_128 := assump_31 assump_141
              apply False.elim assump_128


variable (p0 p4 p5 p7 p2 : Prop)
theorem file12_33216 : (((((True ∨ True) ∨ (p0 → p7)) → False) → (((p5 ∧ p7) ∧ (p2 ∨ True)) → False)) ∨ ((((p2 → False) ∨ (p4 ∨ p7)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case inl assump_11 =>
        have assump_29 : ((True ∨ True) ∨ (p0 → p7)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_17 := assump_1 assump_29
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_30 : ((True ∨ True) ∨ (p0 → p7)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_25 := assump_1 assump_30
        apply False.elim assump_25


variable (p1 p3 p2 p6 p7 : Prop)
theorem file12_34062 : (((((True ∨ p3) ∧ (True ∧ p7)) → ((p1 ∨ p6) → False)) ∧ (((p2 ∧ p2) ∧ (p6 ∧ p1)) ∧ ((True ∨ p6) → False))) → False) := by
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
          case intro assump_16 assump_17 =>
            have assump_28 : (True ∨ p6) := by
              apply Or.inl
              apply True.intro
            let assump_24 := assump_7 assump_28
            apply False.elim assump_24


variable (p5 p4 p2 p3 p1 p7 : Prop)
theorem file12_34752 : ((((((p1 ∧ p5) ∨ (p2 → False)) ∧ ((p5 ∧ p4) → (p7 ∧ p4))) → (((p5 → p7) ∧ (p7 ∧ False)) → ((True ∨ p3) → (p2 → False)))) → False) → False) := by
  intro assump_5
  have assump_44 : ((((p1 ∧ p5) ∨ (p2 → False)) ∧ ((p5 ∧ p4) → (p7 ∧ p4))) → (((p5 → p7) ∧ (p7 ∧ False)) → ((True ∨ p3) → (p2 → False)))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    intro assump_12
    cases assump_11
    case inl assump_15 =>
      cases assump_10
      case intro assump_19 assump_20 =>
        cases assump_20
        case intro assump_23 assump_24 =>
          apply False.elim assump_24
    case inr assump_16 =>
      cases assump_10
      case intro assump_31 assump_32 =>
        cases assump_32
        case intro assump_35 assump_36 =>
          apply False.elim assump_36
  let assump_8 := assump_5 assump_44
  apply False.elim assump_8


variable (p1 p2 p6 p4 p5 p7 p3 : Prop)
theorem file12_35667 : (((((True → False) → (p6 → False)) → False) → False) ∧ ((((p2 → False) → (False → p7)) ∧ ((p7 → p4) → (p1 → p6))) → (((True ∨ p3) ∧ (p5 ∨ p1)) → ((p1 → False) → (True ∨ p1))))) := by
  apply And.intro
  intro assump_9
  have assump_75 : ((True → False) → (p6 → False)) := by
    intro assump_13
    intro assump_14
    have assump_76 : True := by
      apply True.intro
    let assump_19 := assump_13 assump_76
    apply False.elim assump_19
  let assump_12 := assump_9 assump_75
  apply False.elim assump_12
  intro assump_26
  intro assump_27
  intro assump_28
  cases assump_27
  case intro assump_31 assump_32 =>
    cases assump_31
    case inl assump_33 =>
      cases assump_32
      case inl assump_37 =>
        cases assump_26
        case intro assump_41 assump_42 =>
          apply Or.inl
          apply True.intro
      case inr assump_38 =>
        cases assump_26
        case intro assump_49 assump_50 =>
          apply Or.inl
          apply True.intro
    case inr assump_34 =>
      cases assump_32
      case inl assump_57 =>
        cases assump_26
        case intro assump_61 assump_62 =>
          apply Or.inl
          apply True.intro
      case inr assump_58 =>
        cases assump_26
        case intro assump_69 assump_70 =>
          apply Or.inl
          apply True.intro


variable (p4 p6 p5 p3 p7 p1 : Prop)
theorem file12_37036 : ((((((p7 ∨ True) ∧ (p6 → p7)) ∨ ((p3 ∧ p4) ∧ (False ∧ p5))) ∧ (((True → p5) → (p5 ∧ p3)) → ((p6 ∧ True) ∨ (p3 → p3)))) ∧ ((((p1 ∧ False) ∧ (p5 ∧ p4)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case inl assump_10 =>
            have assump_66 : (((p1 ∧ False) ∧ (p5 ∧ p4)) → False) := by
              intro assump_21
              cases assump_21
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
            let assump_20 := assump_3 assump_66
            apply False.elim assump_20
          case inr assump_11 =>
            have assump_67 : (((p1 ∧ False) ∧ (p5 ∧ p4)) → False) := by
              intro assump_42
              cases assump_42
              case intro assump_43 assump_44 =>
                cases assump_43
                case intro assump_45 assump_46 =>
                  apply False.elim assump_46
            let assump_41 := assump_3 assump_67
            apply False.elim assump_41
      case inr assump_7 =>
        cases assump_7
        case intro assump_54 assump_55 =>
          cases assump_54
          case intro assump_56 assump_57 =>
            cases assump_55
            case intro assump_62 assump_63 =>
              apply False.elim assump_62


variable (p5 p2 p0 p7 p1 : Prop)
theorem file12_38665 : (((((p0 → False) → (p2 → False)) → False) → (((p1 → False) → (False → False)) ∨ ((p7 → False) ∨ (True → p0)))) ∨ ((((p2 → p1) ∧ (p5 ∨ p7)) ∨ ((False ∧ p5) → (True ∨ True))) ∨ (((False → False) → False) ∨ ((p1 → False) ∨ (False → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p5 p3 p2 p0 p4 p7 p1 : Prop)
theorem file12_39083 : (((((True → True) → False) → False) ∨ (((p4 ∨ p3) ∨ (p2 → p7)) ∨ ((p3 ∧ p5) → (p2 → False)))) ∧ ((((False ∨ False) → (p0 → p4)) → False) → (((p4 → False) ∧ (p4 ∧ p0)) ∧ ((p0 ∨ p1) → (False ∨ p7))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  have assump_100 : (True → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_100
  apply False.elim assump_4
  intro assump_9
  apply And.intro
  apply And.intro
  intro assump_10
  have assump_101 : ((False ∨ False) → (p0 → p4)) := by
    intro assump_16
    intro assump_17
    cases assump_16
    case inl assump_20 =>
      apply False.elim assump_20
    case inr assump_21 =>
      apply False.elim assump_21
  let assump_15 := assump_9 assump_101
  apply False.elim assump_15
  apply And.intro
  have assump_102 : ((False ∨ False) → (p0 → p4)) := by
    intro assump_32
    intro assump_33
    cases assump_32
    case inl assump_36 =>
      apply False.elim assump_36
    case inr assump_37 =>
      apply False.elim assump_37
  let assump_31 := assump_9 assump_102
  apply False.elim assump_31
  have assump_103 : ((False ∨ False) → (p0 → p4)) := by
    intro assump_48
    intro assump_49
    cases assump_48
    case inl assump_52 =>
      apply False.elim assump_52
    case inr assump_53 =>
      apply False.elim assump_53
  let assump_47 := assump_9 assump_103
  apply False.elim assump_47
  intro assump_61
  cases assump_61
  case inl assump_62 =>
    have assump_104 : ((False ∨ False) → (p0 → p4)) := by
      intro assump_69
      intro assump_70
      cases assump_69
      case inl assump_73 =>
        apply False.elim assump_73
      case inr assump_74 =>
        apply False.elim assump_74
    let assump_68 := assump_9 assump_104
    apply False.elim assump_68
  case inr assump_63 =>
    have assump_105 : ((False ∨ False) → (p0 → p4)) := by
      intro assump_87
      intro assump_88
      cases assump_87
      case inl assump_91 =>
        apply False.elim assump_91
      case inr assump_92 =>
        apply False.elim assump_92
    let assump_86 := assump_9 assump_105
    apply False.elim assump_86


variable (p5 p6 p3 p0 p1 p4 : Prop)
theorem file12_41267 : (((((False ∨ p5) ∨ (p6 → True)) → False) → (((p3 → p0) → False) ∧ ((p4 ∧ True) → False))) ∨ ((((p1 → False) ∨ (False ∨ p0)) → ((p4 ∨ p3) → (p0 ∨ p4))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_26 : ((False ∨ p5) ∨ (p6 → True)) := by
    apply Or.inr
    intro assump_8
    apply True.intro
  let assump_7 := assump_1 assump_26
  apply False.elim assump_7
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    have assump_27 : ((False ∨ p5) ∨ (p6 → True)) := by
      apply Or.inr
      intro assump_22
      apply True.intro
    let assump_21 := assump_1 assump_27
    apply False.elim assump_21


variable (p6 p5 p4 p7 p0 p2 p3 : Prop)
theorem file12_42003 : (((((p5 ∧ False) ∨ (p3 → p6)) → ((p7 ∨ p3) ∨ (p0 → p0))) → False) → ((((p3 → False) ∨ (p4 → False)) → ((p3 ∧ p2) ∧ (p0 → p4))) ∧ (((p2 → True) ∨ (p4 → False)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    have assump_191 : (((p5 ∧ False) ∨ (p3 → p6)) → ((p7 ∨ p3) ∨ (p0 → p0))) := by
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
      case inr assump_12 =>
        apply Or.inr
        intro assump_21
        exact assump_21
    let assump_9 := assump_1 assump_191
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_192 : (((p5 ∧ False) ∨ (p3 → p6)) → ((p7 ∨ p3) ∨ (p0 → p0))) := by
      intro assump_32
      cases assump_32
      case inl assump_33 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          apply False.elim assump_36
      case inr assump_34 =>
        apply Or.inr
        intro assump_43
        exact assump_43
    let assump_31 := assump_1 assump_192
    apply False.elim assump_31
  cases assump_2
  case inl assump_49 =>
    have assump_193 : (((p5 ∧ False) ∨ (p3 → p6)) → ((p7 ∨ p3) ∨ (p0 → p0))) := by
      intro assump_56
      cases assump_56
      case inl assump_57 =>
        cases assump_57
        case intro assump_59 assump_60 =>
          apply False.elim assump_60
      case inr assump_58 =>
        apply Or.inr
        intro assump_67
        exact assump_67
    let assump_55 := assump_1 assump_193
    apply False.elim assump_55
  case inr assump_50 =>
    have assump_194 : (((p5 ∧ False) ∨ (p3 → p6)) → ((p7 ∨ p3) ∨ (p0 → p0))) := by
      intro assump_78
      cases assump_78
      case inl assump_79 =>
        cases assump_79
        case intro assump_81 assump_82 =>
          apply False.elim assump_82
      case inr assump_80 =>
        apply Or.inr
        intro assump_89
        exact assump_89
    let assump_77 := assump_1 assump_194
    apply False.elim assump_77
  intro assump_95
  cases assump_2
  case inl assump_98 =>
    have assump_195 : (((p5 ∧ False) ∨ (p3 → p6)) → ((p7 ∨ p3) ∨ (p0 → p0))) := by
      intro assump_105
      cases assump_105
      case inl assump_106 =>
        cases assump_106
        case intro assump_108 assump_109 =>
          apply False.elim assump_109
      case inr assump_107 =>
        apply Or.inr
        intro assump_116
        exact assump_116
    let assump_104 := assump_1 assump_195
    apply False.elim assump_104
  case inr assump_99 =>
    have assump_196 : (((p5 ∧ False) ∨ (p3 → p6)) → ((p7 ∨ p3) ∨ (p0 → p0))) := by
      intro assump_127
      cases assump_127
      case inl assump_128 =>
        cases assump_128
        case intro assump_130 assump_131 =>
          apply False.elim assump_131
      case inr assump_129 =>
        apply Or.inr
        intro assump_138
        exact assump_138
    let assump_126 := assump_1 assump_196
    apply False.elim assump_126
  intro assump_144
  cases assump_144
  case inl assump_145 =>
    have assump_197 : (((p5 ∧ False) ∨ (p3 → p6)) → ((p7 ∨ p3) ∨ (p0 → p0))) := by
      intro assump_152
      cases assump_152
      case inl assump_153 =>
        cases assump_153
        case intro assump_155 assump_156 =>
          apply False.elim assump_156
      case inr assump_154 =>
        apply Or.inr
        intro assump_163
        exact assump_163
    let assump_151 := assump_1 assump_197
    apply False.elim assump_151
  case inr assump_146 =>
    have assump_198 : (((p5 ∧ False) ∨ (p3 → p6)) → ((p7 ∨ p3) ∨ (p0 → p0))) := by
      intro assump_174
      cases assump_174
      case inl assump_175 =>
        cases assump_175
        case intro assump_177 assump_178 =>
          apply False.elim assump_178
      case inr assump_176 =>
        apply Or.inr
        intro assump_185
        exact assump_185
    let assump_173 := assump_1 assump_198
    apply False.elim assump_173


variable (p0 p4 p3 p1 p7 : Prop)
theorem file12_46085 : (((((p4 → p7) → False) ∧ ((p4 ∨ p0) → False)) ∧ (((p3 → False) → (p3 → p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_26 : ((p3 → False) → (p3 → p1)) := by
        intro assump_13
        intro assump_14
        have assump_27 : p3 := by
          exact assump_14
        let assump_19 := assump_13 assump_27
        apply False.elim assump_19
      let assump_12 := assump_3 assump_26
      apply False.elim assump_12


variable (p0 p6 p5 p1 p7 p2 : Prop)
theorem file12_46688 : (((((False → False) → False) → False) → False) → ((((p5 ∨ p1) → False) ∧ ((True → p6) → (p0 → p5))) ∨ (((p2 ∨ p6) ∧ (True ∨ p7)) ∧ ((True ∨ p5) → (p0 → False))))) := by
  intro assump_10
  apply Or.inl
  apply And.intro
  intro assump_13
  cases assump_13
  case inl assump_14 =>
    have assump_73 : (((False → False) → False) → False) := by
      intro assump_20
      have assump_74 : (False → False) := by
        intro assump_24
        apply False.elim assump_24
      let assump_23 := assump_20 assump_74
      apply False.elim assump_23
    let assump_19 := assump_10 assump_73
    apply False.elim assump_19
  case inr assump_15 =>
    have assump_75 : (((False → False) → False) → False) := by
      intro assump_37
      have assump_76 : (False → False) := by
        intro assump_41
        apply False.elim assump_41
      let assump_40 := assump_37 assump_76
      apply False.elim assump_40
    let assump_36 := assump_10 assump_75
    apply False.elim assump_36
  intro assump_50
  intro assump_51
  have assump_77 : (((False → False) → False) → False) := by
    intro assump_60
    have assump_78 : (False → False) := by
      intro assump_64
      apply False.elim assump_64
    let assump_63 := assump_60 assump_78
    apply False.elim assump_63
  let assump_59 := assump_10 assump_77
  apply False.elim assump_59


variable (p5 p1 p0 p7 p2 p4 p6 p3 : Prop)
theorem file12_48087 : (((((p1 → p4) ∨ (p4 ∧ p3)) ∨ ((p0 ∨ p6) ∨ (p3 → False))) → (((True → False) ∧ (p5 ∨ p6)) → ((p7 → p0) ∨ (p5 ∨ p4)))) ∨ ((((p2 → False) ∨ (p1 → p5)) → False) ∧ (((p1 ∧ False) ∧ (p2 → p2)) ∧ ((False → False) ∨ (p5 → p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          intro assump_17
          have assump_145 : True := by
            apply True.intro
          let assump_23 := assump_3 assump_145
          apply False.elim assump_23
        case inr assump_14 =>
          cases assump_14
          case intro assump_27 assump_28 =>
            apply Or.inl
            intro assump_33
            have assump_146 : True := by
              apply True.intro
            let assump_40 := assump_3 assump_146
            apply False.elim assump_40
      case inr assump_12 =>
        cases assump_12
        case inl assump_44 =>
          cases assump_44
          case inl assump_46 =>
            apply Or.inl
            intro assump_50
            exact assump_46
          case inr assump_47 =>
            apply Or.inl
            intro assump_55
            have assump_147 : True := by
              apply True.intro
            let assump_61 := assump_3 assump_147
            apply False.elim assump_61
        case inr assump_45 =>
          apply Or.inl
          intro assump_67
          have assump_148 : True := by
            apply True.intro
          let assump_73 := assump_3 assump_148
          apply False.elim assump_73
    case inr assump_8 =>
      cases assump_1
      case inl assump_79 =>
        cases assump_79
        case inl assump_81 =>
          apply Or.inl
          intro assump_85
          have assump_149 : True := by
            apply True.intro
          let assump_91 := assump_3 assump_149
          apply False.elim assump_91
        case inr assump_82 =>
          cases assump_82
          case intro assump_95 assump_96 =>
            apply Or.inl
            intro assump_101
            have assump_150 : True := by
              apply True.intro
            let assump_108 := assump_3 assump_150
            apply False.elim assump_108
      case inr assump_80 =>
        cases assump_80
        case inl assump_112 =>
          cases assump_112
          case inl assump_114 =>
            apply Or.inl
            intro assump_118
            exact assump_114
          case inr assump_115 =>
            apply Or.inl
            intro assump_123
            have assump_151 : True := by
              apply True.intro
            let assump_129 := assump_3 assump_151
            apply False.elim assump_129
        case inr assump_113 =>
          apply Or.inl
          intro assump_135
          have assump_152 : True := by
            apply True.intro
          let assump_141 := assump_3 assump_152
          apply False.elim assump_141


variable (p3 p7 p0 p1 p4 : Prop)
theorem file12_51185 : (((((True ∨ p3) ∨ (False → False)) → False) → (((p4 → p4) → (p3 ∨ p7)) → False)) ∨ ((((p3 → p0) ∨ (p3 → False)) → False) → (((p4 ∨ p7) ∧ (p1 ∨ p7)) ∧ ((p4 ∧ p1) ∧ (p4 ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : ((True ∨ p3) ∨ (False → False)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p1 p2 p7 p0 : Prop)
theorem file12_51648 : ((((((False ∧ p2) → False) ∨ ((p0 ∧ True) → (p1 ∨ p2))) ∨ (((p0 → p0) → False) ∨ ((p7 ∧ p1) ∧ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p2) → False) ∨ ((p0 ∧ True) → (p1 ∨ p2))) ∨ (((p0 → p0) → False) ∨ ((p7 ∧ p1) ∧ (True → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p4 p7 p0 p2 : Prop)
theorem file12_52198 : ((((((p4 → False) ∨ (p0 → p2)) ∨ ((True → False) → (p3 ∧ p2))) → (((False → False) ∨ (False ∨ p4)) → ((True → True) ∧ (p7 → p7)))) → False) → False) := by
  intro assump_22
  have assump_65 : ((((p4 → False) ∨ (p0 → p2)) ∨ ((True → False) → (p3 ∧ p2))) → (((False → False) ∨ (False ∨ p4)) → ((True → True) ∧ (p7 → p7)))) := by
    intro assump_26
    intro assump_27
    apply And.intro
    intro assump_28
    apply True.intro
    intro assump_29
    cases assump_27
    case inl assump_32 =>
      cases assump_26
      case inl assump_36 =>
        cases assump_36
        case inl assump_38 =>
          exact assump_29
        case inr assump_39 =>
          exact assump_29
      case inr assump_37 =>
        exact assump_29
    case inr assump_33 =>
      cases assump_33
      case inl assump_46 =>
        apply False.elim assump_46
      case inr assump_47 =>
        cases assump_26
        case inl assump_52 =>
          cases assump_52
          case inl assump_54 =>
            exact assump_29
          case inr assump_55 =>
            exact assump_29
        case inr assump_53 =>
          exact assump_29
  let assump_25 := assump_22 assump_65
  apply False.elim assump_25


variable (p1 p7 p0 p6 p5 : Prop)
theorem file12_53450 : ((((((p0 → False) → False) → False) → False) ∧ ((((p1 ∨ p1) ∨ (p5 → False)) → ((p6 ∨ p1) ∨ (p7 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p1 ∨ p1) ∨ (p5 → False)) → ((p6 ∨ p1) ∨ (p7 → True))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inl
          apply Or.inr
          exact assump_12
        case inr assump_13 =>
          apply Or.inl
          apply Or.inr
          exact assump_13
      case inr assump_11 =>
        apply Or.inr
        intro assump_20
        apply True.intro
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p2 p5 p6 p3 p7 p1 p0 p4 : Prop)
theorem file12_54263 : (((((p0 → True) ∧ (True → p5)) ∧ ((p0 → p5) ∧ (p1 ∨ p3))) → (((p4 → p1) → False) → ((False → p4) → (p2 → False)))) → ((((p3 ∧ p2) → (True ∨ p2)) ∨ ((True ∧ p5) → (False → p7))) ∨ (((False → p7) ∧ (p2 ∨ p0)) ∨ ((p1 → p6) → (p3 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inl
    apply True.intro


variable (p5 p0 p4 p2 p3 p1 p7 : Prop)
theorem file12_54724 : (((((p4 ∧ p5) → (p4 ∨ p3)) → False) ∧ (((p1 ∧ p7) ∧ (False ∧ p2)) ∧ ((p4 ∨ p0) → False))) → False) := by
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
          case intro assump_16 assump_17 =>
            apply False.elim assump_16


variable (p5 p6 p4 p0 p3 p1 : Prop)
theorem file12_55244 : (((((p1 → False) → (p3 ∨ p4)) → ((p5 ∨ False) → (True ∧ p5))) ∧ (((True → False) → False) → False)) → ((((p4 → False) → False) → False) ∧ (((p0 ∧ p6) ∧ (p5 ∧ p5)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_54 : ((True → False) → False) := by
      intro assump_12
      have assump_55 : True := by
        apply True.intro
      let assump_15 := assump_12 assump_55
      apply False.elim assump_15
    let assump_11 := assump_6 assump_54
    apply False.elim assump_11
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_23
    case intro assump_25 assump_26 =>
      cases assump_24
      case intro assump_31 assump_32 =>
        cases assump_1
        case intro assump_37 assump_38 =>
          have assump_56 : ((True → False) → False) := by
            intro assump_44
            have assump_57 : True := by
              apply True.intro
            let assump_47 := assump_44 assump_57
            apply False.elim assump_47
          let assump_43 := assump_38 assump_56
          apply False.elim assump_43


variable (p4 p1 p7 p3 p5 p6 : Prop)
theorem file12_56453 : (((((p4 ∧ p6) ∧ (p4 → False)) → False) → False) → ((((False → p5) ∨ (True → p1)) ∨ ((p3 → p7) → (p6 ∨ False))) → (((False ∧ p5) ∨ (p7 → p3)) ∨ ((False ∨ p4) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      apply Or.inr
      intro assump_11
      have assump_88 : (((p4 ∧ p6) ∧ (p4 → False)) → False) := by
        intro assump_16
        cases assump_16
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            have assump_89 : p4 := by
              exact assump_19
            let assump_27 := assump_18 assump_89
            apply False.elim assump_27
      let assump_15 := assump_1 assump_88
      apply False.elim assump_15
    case inr assump_6 =>
      apply Or.inl
      apply Or.inr
      intro assump_38
      have assump_90 : (((p4 ∧ p6) ∧ (p4 → False)) → False) := by
        intro assump_43
        cases assump_43
        case intro assump_44 assump_45 =>
          cases assump_44
          case intro assump_46 assump_47 =>
            have assump_91 : p4 := by
              exact assump_46
            let assump_54 := assump_45 assump_91
            apply False.elim assump_54
      let assump_42 := assump_1 assump_90
      apply False.elim assump_42
  case inr assump_4 =>
    apply Or.inl
    apply Or.inr
    intro assump_65
    have assump_92 : (((p4 ∧ p6) ∧ (p4 → False)) → False) := by
      intro assump_70
      cases assump_70
      case intro assump_71 assump_72 =>
        cases assump_71
        case intro assump_73 assump_74 =>
          have assump_93 : p4 := by
            exact assump_73
          let assump_81 := assump_72 assump_93
          apply False.elim assump_81
    let assump_69 := assump_1 assump_92
    apply False.elim assump_69


variable (p7 p3 p2 p1 p4 : Prop)
theorem file12_58372 : (((((False → False) ∨ (p7 → False)) → ((False → False) → False)) → False) ∨ ((((p2 ∨ p1) → (p3 ∨ p3)) → ((True ∨ p4) → False)) → False)) := by
  apply Or.inl
  intro assump_19
  have assump_33 : ((False → False) ∨ (p7 → False)) := by
    apply Or.inl
    intro assump_23
    apply False.elim assump_23
  let assump_22 := assump_19 assump_33
  have assump_34 : (False → False) := by
    intro assump_27
    apply False.elim assump_27
  let assump_26 := assump_22 assump_34
  apply False.elim assump_26


variable (p7 p2 p6 p1 p4 p0 p5 : Prop)
theorem file12_58936 : (((((p4 ∨ p0) → False) → ((False → p5) ∨ (p5 ∧ p1))) ∨ (((p7 ∨ p2) → False) → ((True ∨ p4) → (p5 ∨ p4)))) ∧ ((((p2 ∨ p6) ∧ (True → False)) ∧ ((False ∧ p6) ∧ (False → False))) → False)) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_9
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
      case inr assump_13 =>
        cases assump_9
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            apply False.elim assump_30


variable (p3 p1 p7 p4 : Prop)
theorem file12_59842 : (((((p3 → p1) ∧ (p3 ∧ False)) → ((p7 → p3) ∨ (p1 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p3 → p1) ∧ (p3 ∧ False)) → ((p7 → p3) ∨ (p1 ∨ p4))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p5 p0 p7 p4 : Prop)
theorem file12_60312 : (((((p5 ∨ p4) ∧ (p4 → False)) ∧ ((p2 → False) ∧ (p4 → False))) ∨ (((True → False) ∧ (p4 → False)) → ((True → p7) → False))) ∨ ((((p0 → p5) → (p5 → False)) ∧ ((False → False) ∨ (p5 ∧ p7))) → False)) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_16 : True := by
      apply True.intro
    let assump_12 := assump_5 assump_16
    apply False.elim assump_12


variable (p0 p2 p5 p3 p4 p6 : Prop)
theorem file12_60817 : (((((p2 ∨ p4) ∧ (p5 ∨ p5)) → False) → False) → ((((p4 → False) ∧ (p2 → False)) → ((p6 → p0) → (True → False))) ∨ (((p3 ∨ p4) ∨ (p3 ∧ True)) ∧ ((True ∨ p4) → (p5 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_4
  case intro assump_11 assump_12 =>
    have assump_71 : (((p2 ∨ p4) ∧ (p5 ∨ p5)) → False) := by
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        cases assump_22
        case inl assump_24 =>
          cases assump_23
          case inl assump_28 =>
            have assump_72 : p2 := by
              exact assump_24
            let assump_34 := assump_12 assump_72
            apply False.elim assump_34
          case inr assump_29 =>
            have assump_73 : p2 := by
              exact assump_24
            let assump_42 := assump_12 assump_73
            apply False.elim assump_42
        case inr assump_25 =>
          cases assump_23
          case inl assump_48 =>
            have assump_74 : p4 := by
              exact assump_25
            let assump_55 := assump_11 assump_74
            apply False.elim assump_55
          case inr assump_49 =>
            have assump_75 : p4 := by
              exact assump_25
            let assump_64 := assump_11 assump_75
            apply False.elim assump_64
    let assump_20 := assump_1 assump_71
    apply False.elim assump_20


variable (p2 p1 p7 p0 : Prop)
theorem file12_62291 : (((((p0 → p1) → (p2 ∨ p0)) → ((False ∨ True) ∨ (p2 → p7))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p0 → p1) → (p2 ∨ p0)) → ((False ∨ True) ∨ (p2 → p7))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p7 p4 p5 p2 p3 : Prop)
theorem file12_62672 : (((((p2 → p2) → False) ∨ ((False → False) → (p2 ∧ p3))) → False) → ((((True → p0) → False) → False) → (((p7 ∧ False) ∧ (p7 → p2)) → ((p3 ∨ p5) ∨ (p5 ∨ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p7 p2 p4 p0 p3 : Prop)
theorem file12_63083 : ((((((True ∨ p7) → False) ∧ ((p2 ∧ p2) → False)) → (((p4 ∧ p4) ∨ (p0 → p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_42 : ((((True ∨ p7) → False) ∧ ((p2 ∧ p2) → False)) → (((p4 ∧ p4) ∨ (p0 → p3)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_5
        case intro assump_15 assump_16 =>
          have assump_43 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_22 := assump_15 assump_43
          apply False.elim assump_22
    case inr assump_8 =>
      cases assump_5
      case intro assump_28 assump_29 =>
        have assump_44 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_35 := assump_28 assump_44
        apply False.elim assump_35
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p0 p4 p1 p3 p2 p5 p6 p7 : Prop)
theorem file12_64099 : (((((p1 ∨ p3) ∨ (p3 ∨ False)) ∨ ((p7 ∧ True) → False)) → (((False → p0) → (p6 → False)) → ((p6 ∧ p2) → (p3 ∨ p0)))) → ((((p7 ∧ p4) ∧ (p5 → False)) ∧ ((False ∧ p3) → (p5 ∨ p5))) ∨ (((p4 ∨ p4) → (p7 ∧ p3)) → ((p1 ∨ p1) ∨ (True ∧ True))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  apply Or.inr
  apply And.intro
  apply True.intro
  apply True.intro


variable (p5 p7 p3 p2 p6 p4 p0 : Prop)
theorem file12_64525 : (((((False → p0) ∧ (p6 ∧ False)) → ((p4 ∨ p5) → (True ∧ p3))) → False) → ((((p7 → False) → False) ∧ ((p0 ∧ p2) → (False → p3))) ∨ (((p6 → p6) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_44 : (((False → p0) ∧ (p6 ∧ False)) → ((p4 ∨ p5) → (True ∧ p3))) := by
    intro assump_9
    intro assump_10
    apply And.intro
    apply True.intro
    cases assump_10
    case inl assump_11 =>
      cases assump_9
      case intro assump_15 assump_16 =>
        cases assump_16
        case intro assump_19 assump_20 =>
          apply False.elim assump_20
    case inr assump_12 =>
      cases assump_9
      case intro assump_27 assump_28 =>
        cases assump_28
        case intro assump_31 assump_32 =>
          apply False.elim assump_32
  let assump_8 := assump_1 assump_44
  apply False.elim assump_8
  intro assump_40
  intro assump_41
  apply False.elim assump_41


variable (p2 p3 p0 p7 p1 p6 p5 : Prop)
theorem file12_65518 : (((((False ∧ p1) → (True ∧ p2)) → False) → False) ∨ ((((p6 ∧ False) ∧ (p7 ∨ p3)) ∨ ((p0 → p3) → False)) → (((p1 ∨ p6) ∧ (p5 ∨ False)) → ((True → False) ∧ (p2 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_13 : ((False ∧ p1) → (True ∧ p2)) := by
    intro assump_5
    apply And.intro
    apply True.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p4 p5 p0 p3 p2 p1 : Prop)
theorem file12_66053 : (((((p5 → False) → False) → ((p1 ∨ p1) ∨ (p0 → p3))) → False) → ((((False ∧ p3) ∧ (p3 → False)) ∧ ((True → False) ∧ (p0 ∨ p0))) → (((p2 → False) ∨ (p4 ∨ p2)) ∧ ((p1 ∧ p4) ∨ (p4 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7
  cases assump_2
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_15


variable (p1 p0 p3 p5 p7 p6 p2 : Prop)
theorem file12_66768 : ((((((True → False) → (p6 → False)) ∨ ((p2 ∧ p5) → False)) ∧ (((p7 ∨ p7) ∨ (False ∨ p0)) ∨ ((p2 → p1) ∨ (p6 ∨ p6)))) ∧ ((((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) → False)) → False) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_16
      case inl assump_18 =>
        cases assump_17
        case inl assump_22 =>
          cases assump_22
          case inl assump_24 =>
            cases assump_24
            case inl assump_26 =>
              have assump_208 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_33
                intro assump_34
                intro assump_35
                apply False.elim assump_35
              let assump_32 := assump_15 assump_208
              apply False.elim assump_32
            case inr assump_27 =>
              have assump_209 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_46
                intro assump_47
                intro assump_48
                apply False.elim assump_48
              let assump_45 := assump_15 assump_209
              apply False.elim assump_45
          case inr assump_25 =>
            cases assump_25
            case inl assump_54 =>
              apply False.elim assump_54
            case inr assump_55 =>
              have assump_210 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_63
                intro assump_64
                intro assump_65
                apply False.elim assump_65
              let assump_62 := assump_15 assump_210
              apply False.elim assump_62
        case inr assump_23 =>
          cases assump_23
          case inl assump_71 =>
            have assump_211 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
              intro assump_78
              intro assump_79
              intro assump_80
              apply False.elim assump_80
            let assump_77 := assump_15 assump_211
            apply False.elim assump_77
          case inr assump_72 =>
            cases assump_72
            case inl assump_86 =>
              have assump_212 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_93
                intro assump_94
                intro assump_95
                apply False.elim assump_95
              let assump_92 := assump_15 assump_212
              apply False.elim assump_92
            case inr assump_87 =>
              have assump_213 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_106
                intro assump_107
                intro assump_108
                apply False.elim assump_108
              let assump_105 := assump_15 assump_213
              apply False.elim assump_105
      case inr assump_19 =>
        cases assump_17
        case inl assump_116 =>
          cases assump_116
          case inl assump_118 =>
            cases assump_118
            case inl assump_120 =>
              have assump_214 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_127
                intro assump_128
                intro assump_129
                apply False.elim assump_129
              let assump_126 := assump_15 assump_214
              apply False.elim assump_126
            case inr assump_121 =>
              have assump_215 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_140
                intro assump_141
                intro assump_142
                apply False.elim assump_142
              let assump_139 := assump_15 assump_215
              apply False.elim assump_139
          case inr assump_119 =>
            cases assump_119
            case inl assump_148 =>
              apply False.elim assump_148
            case inr assump_149 =>
              have assump_216 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_157
                intro assump_158
                intro assump_159
                apply False.elim assump_159
              let assump_156 := assump_15 assump_216
              apply False.elim assump_156
        case inr assump_117 =>
          cases assump_117
          case inl assump_165 =>
            have assump_217 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
              intro assump_172
              intro assump_173
              intro assump_174
              apply False.elim assump_174
            let assump_171 := assump_15 assump_217
            apply False.elim assump_171
          case inr assump_166 =>
            cases assump_166
            case inl assump_180 =>
              have assump_218 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_187
                intro assump_188
                intro assump_189
                apply False.elim assump_189
              let assump_186 := assump_15 assump_218
              apply False.elim assump_186
            case inr assump_181 =>
              have assump_219 : (((p3 ∨ p2) → (p1 ∨ p0)) → ((p3 ∧ True) → (False → False))) := by
                intro assump_200
                intro assump_201
                intro assump_202
                apply False.elim assump_202
              let assump_199 := assump_15 assump_219
              apply False.elim assump_199


variable (p5 p1 p4 p6 p0 p3 p7 : Prop)
theorem file12_72422 : ((((((p1 → False) ∧ (p5 ∨ p0)) → ((p5 → False) → (p6 ∨ False))) ∧ (((True ∨ p7) ∧ (False → p4)) → False)) ∧ ((((p7 → False) ∨ (p5 → False)) ∧ ((p5 ∧ p1) ∨ (p0 → p3))) ∨ (((p4 → p4) → False) ∨ ((p7 → False) ∨ (p7 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case inl assump_18 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                have assump_103 : ((True ∨ p7) ∧ (False → p4)) := by
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  intro assump_30
                  apply False.elim assump_30
                let assump_29 := assump_5 assump_103
                apply False.elim assump_29
            case inr assump_19 =>
              have assump_104 : ((True ∨ p7) ∧ (False → p4)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_41
                apply False.elim assump_41
              let assump_40 := assump_5 assump_104
              apply False.elim assump_40
          case inr assump_15 =>
            cases assump_13
            case inl assump_49 =>
              cases assump_49
              case intro assump_51 assump_52 =>
                have assump_105 : p5 := by
                  exact assump_51
                let assump_59 := assump_15 assump_105
                apply False.elim assump_59
            case inr assump_50 =>
              have assump_106 : ((True ∨ p7) ∧ (False → p4)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_68
                apply False.elim assump_68
              let assump_67 := assump_5 assump_106
              apply False.elim assump_67
      case inr assump_11 =>
        cases assump_11
        case inl assump_74 =>
          have assump_107 : (p4 → p4) := by
            intro assump_79
            exact assump_79
          let assump_78 := assump_74 assump_107
          apply False.elim assump_78
        case inr assump_75 =>
          cases assump_75
          case inl assump_85 =>
            have assump_108 : ((True ∨ p7) ∧ (False → p4)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_91
              apply False.elim assump_91
            let assump_90 := assump_5 assump_108
            apply False.elim assump_90
          case inr assump_86 =>
            cases assump_86
            case intro assump_97 assump_98 =>
              apply False.elim assump_98


variable (p0 p1 p2 p6 p3 p7 p4 p5 : Prop)
theorem file12_75392 : ((((((p3 ∧ p6) ∨ (p2 → p0)) → ((False ∧ True) ∧ (p2 ∧ True))) → False) ∧ ((((p6 ∨ p7) ∨ (p7 ∧ p7)) ∨ ((p6 → False) ∨ (p2 ∨ p3))) ∧ (((p7 → False) → (p4 → False)) ∧ ((p5 ∧ False) ∧ (p3 → p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  apply False.elim assump_23
          case inr assump_13 =>
            cases assump_7
            case intro assump_30 assump_31 =>
              cases assump_31
              case intro assump_34 assump_35 =>
                cases assump_34
                case intro assump_36 assump_37 =>
                  apply False.elim assump_37
        case inr assump_11 =>
          cases assump_11
          case intro assump_42 assump_43 =>
            cases assump_7
            case intro assump_48 assump_49 =>
              cases assump_49
              case intro assump_52 assump_53 =>
                cases assump_52
                case intro assump_54 assump_55 =>
                  apply False.elim assump_55
      case inr assump_9 =>
        cases assump_9
        case inl assump_60 =>
          cases assump_7
          case intro assump_64 assump_65 =>
            cases assump_65
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                apply False.elim assump_71
        case inr assump_61 =>
          cases assump_61
          case inl assump_76 =>
            cases assump_7
            case intro assump_80 assump_81 =>
              cases assump_81
              case intro assump_84 assump_85 =>
                cases assump_84
                case intro assump_86 assump_87 =>
                  apply False.elim assump_87
          case inr assump_77 =>
            cases assump_7
            case intro assump_94 assump_95 =>
              cases assump_95
              case intro assump_98 assump_99 =>
                cases assump_98
                case intro assump_100 assump_101 =>
                  apply False.elim assump_101


variable (p2 p5 p3 p4 p1 : Prop)
theorem file12_77929 : ((((((True → True) ∨ (p5 ∨ True)) ∨ ((p4 ∨ p3) ∧ (p5 → p2))) ∨ (((p5 → False) ∧ (p5 → p5)) ∧ ((p3 → False) ∨ (False → p1)))) → False) → False) := by
  intro assump_1
  have assump_9 : ((((True → True) ∨ (p5 ∨ True)) ∨ ((p4 ∨ p3) ∧ (p5 → p2))) ∨ (((p5 → False) ∧ (p5 → p5)) ∧ ((p3 → False) ∨ (False → p1)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p3 p5 p1 p2 : Prop)
theorem file12_78451 : ((((((True ∨ p2) → False) → False) ∧ (((p5 ∨ p3) ∧ (p3 ∨ True)) → ((True → False) → (p1 ∨ p5)))) → False) → False) := by
  intro assump_9
  have assump_58 : ((((True ∨ p2) → False) → False) ∧ (((p5 ∨ p3) ∧ (p3 ∨ True)) → ((True → False) → (p1 ∨ p5)))) := by
    apply And.intro
    intro assump_13
    have assump_59 : (True ∨ p2) := by
      apply Or.inl
      apply True.intro
    let assump_16 := assump_13 assump_59
    apply False.elim assump_16
    intro assump_20
    intro assump_21
    cases assump_20
    case intro assump_24 assump_25 =>
      cases assump_24
      case inl assump_26 =>
        cases assump_25
        case inl assump_30 =>
          apply Or.inr
          exact assump_26
        case inr assump_31 =>
          apply Or.inr
          exact assump_26
      case inr assump_27 =>
        cases assump_25
        case inl assump_38 =>
          have assump_60 : True := by
            apply True.intro
          let assump_44 := assump_21 assump_60
          apply False.elim assump_44
        case inr assump_39 =>
          have assump_61 : True := by
            apply True.intro
          let assump_51 := assump_21 assump_61
          apply False.elim assump_51
  let assump_12 := assump_9 assump_58
  apply False.elim assump_12


variable (p1 p7 p0 p6 p2 : Prop)
theorem file12_79770 : ((((((p0 → False) ∧ (True ∧ p7)) ∧ ((p2 ∧ False) → False)) → False) ∧ ((((p1 → False) ∧ (p6 → False)) → ((p7 ∧ p0) → (p0 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p1 → False) ∧ (p6 → False)) → ((p7 ∧ p0) → (p0 → True))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p1 p5 p7 p6 p3 p4 : Prop)
theorem file12_80298 : ((((((p4 → False) ∨ (p1 → p7)) ∧ ((False ∨ p5) → False)) → (((p6 ∧ p5) ∨ (p3 ∨ p6)) → ((True → False) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p4 → False) ∨ (p1 → p7)) ∧ ((False ∨ p5) → False)) → (((p6 ∧ p5) ∨ (p3 ∨ p6)) → ((True → False) → (False → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p0 p4 p2 p7 p5 : Prop)
theorem file12_80839 : (((((p4 ∨ True) → (p7 ∧ p5)) ∧ ((p5 → False) ∨ (p6 ∧ p2))) ∧ (((p7 → p0) → False) ∧ ((p2 → False) ∧ (False ∧ p0)))) → ((((False → False) → False) ∧ ((p7 ∧ True) ∧ (p0 → p2))) ∧ (((p0 → True) ∨ (False ∨ p0)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_6
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            cases assump_20
            case intro assump_23 assump_24 =>
              apply False.elim assump_23
      case inr assump_12 =>
        cases assump_12
        case intro assump_27 assump_28 =>
          cases assump_6
          case intro assump_33 assump_34 =>
            cases assump_34
            case intro assump_37 assump_38 =>
              cases assump_38
              case intro assump_41 assump_42 =>
                apply False.elim assump_41
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_45 assump_46 =>
    cases assump_45
    case intro assump_47 assump_48 =>
      cases assump_48
      case inl assump_51 =>
        cases assump_46
        case intro assump_55 assump_56 =>
          cases assump_56
          case intro assump_59 assump_60 =>
            cases assump_60
            case intro assump_63 assump_64 =>
              apply False.elim assump_63
      case inr assump_52 =>
        cases assump_52
        case intro assump_67 assump_68 =>
          cases assump_46
          case intro assump_73 assump_74 =>
            cases assump_74
            case intro assump_77 assump_78 =>
              cases assump_78
              case intro assump_81 assump_82 =>
                apply False.elim assump_81
  apply True.intro
  intro assump_85
  cases assump_1
  case intro assump_88 assump_89 =>
    cases assump_88
    case intro assump_90 assump_91 =>
      cases assump_91
      case inl assump_94 =>
        cases assump_89
        case intro assump_98 assump_99 =>
          cases assump_99
          case intro assump_102 assump_103 =>
            cases assump_103
            case intro assump_106 assump_107 =>
              apply False.elim assump_106
      case inr assump_95 =>
        cases assump_95
        case intro assump_110 assump_111 =>
          cases assump_89
          case intro assump_116 assump_117 =>
            cases assump_117
            case intro assump_120 assump_121 =>
              cases assump_121
              case intro assump_124 assump_125 =>
                apply False.elim assump_124
  intro assump_128
  cases assump_128
  case inl assump_129 =>
    cases assump_1
    case intro assump_133 assump_134 =>
      cases assump_133
      case intro assump_135 assump_136 =>
        cases assump_136
        case inl assump_139 =>
          cases assump_134
          case intro assump_143 assump_144 =>
            cases assump_144
            case intro assump_147 assump_148 =>
              cases assump_148
              case intro assump_151 assump_152 =>
                apply False.elim assump_151
        case inr assump_140 =>
          cases assump_140
          case intro assump_155 assump_156 =>
            cases assump_134
            case intro assump_161 assump_162 =>
              cases assump_162
              case intro assump_165 assump_166 =>
                cases assump_166
                case intro assump_169 assump_170 =>
                  apply False.elim assump_169
  case inr assump_130 =>
    cases assump_130
    case inl assump_173 =>
      apply False.elim assump_173
    case inr assump_174 =>
      cases assump_1
      case intro assump_179 assump_180 =>
        cases assump_179
        case intro assump_181 assump_182 =>
          cases assump_182
          case inl assump_185 =>
            cases assump_180
            case intro assump_189 assump_190 =>
              cases assump_190
              case intro assump_193 assump_194 =>
                cases assump_194
                case intro assump_197 assump_198 =>
                  apply False.elim assump_197
          case inr assump_186 =>
            cases assump_186
            case intro assump_201 assump_202 =>
              cases assump_180
              case intro assump_207 assump_208 =>
                cases assump_208
                case intro assump_211 assump_212 =>
                  cases assump_212
                  case intro assump_215 assump_216 =>
                    apply False.elim assump_215


variable (p2 p0 : Prop)
theorem file12_85515 : (((((p0 → p0) ∨ (True ∨ True)) ∧ ((p2 ∨ False) ∨ (p2 → False))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p0 → p0) ∨ (True ∨ True)) ∧ ((p2 ∨ False) ∨ (p2 → False))) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    exact assump_5
    apply Or.inr
    intro assump_8
    have assump_23 : (((p0 → p0) ∨ (True ∨ True)) ∧ ((p2 ∨ False) ∨ (p2 → False))) := by
      apply And.intro
      apply Or.inl
      intro assump_13
      exact assump_13
      apply Or.inl
      apply Or.inl
      exact assump_8
    let assump_12 := assump_1 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p6 p0 p5 : Prop)
theorem file12_86241 : ((((((p5 ∨ True) ∨ (False ∧ p4)) → False) → (((p0 → p6) → (p6 ∧ True)) → False)) → False) → False) := by
  intro assump_7
  have assump_24 : ((((p5 ∨ True) ∨ (False ∧ p4)) → False) → (((p0 → p6) → (p6 ∧ True)) → False)) := by
    intro assump_11
    intro assump_12
    have assump_25 : ((p5 ∨ True) ∨ (False ∧ p4)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_17 := assump_11 assump_25
    apply False.elim assump_17
  let assump_10 := assump_7 assump_24
  apply False.elim assump_10


variable (p3 p1 p5 : Prop)
theorem file12_86814 : ((((((False ∧ p5) ∧ (p3 ∨ True)) ∧ ((p5 ∧ p3) ∧ (p1 ∧ p5))) → False) → False) → False) := by
  intro assump_36
  have assump_52 : ((((False ∧ p5) ∧ (p3 ∨ True)) ∧ ((p5 ∧ p3) ∧ (p1 ∧ p5))) → False) := by
    intro assump_40
    cases assump_40
    case intro assump_41 assump_42 =>
      cases assump_41
      case intro assump_43 assump_44 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          apply False.elim assump_45
  let assump_39 := assump_36 assump_52
  apply False.elim assump_39


variable (p1 p7 p5 p0 p4 : Prop)
theorem file12_87385 : ((((((True ∨ p0) → False) ∧ ((p1 ∧ p4) ∧ (p5 → p7))) → False) → False) → False) := by
  intro assump_1
  have assump_30 : ((((True ∨ p0) → False) ∧ ((p1 ∧ p4) ∧ (p5 → p7))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_31 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_23 := assump_6 assump_31
          apply False.elim assump_23
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p7 p3 p4 p0 p5 p1 : Prop)
theorem file12_88081 : ((((((p7 → False) ∧ (True → p0)) ∧ ((p3 ∨ p1) ∧ (p7 ∧ p0))) ∨ (((True → p5) ∨ (p3 ∨ p7)) → ((p3 ∧ False) ∧ (p0 ∨ p4)))) ∧ ((((p1 → False) → False) → ((p5 ∧ p1) → (False → p1))) → False)) → False) := by
  intro assump_41
  cases assump_41
  case intro assump_42 assump_43 =>
    cases assump_42
    case inl assump_44 =>
      cases assump_44
      case intro assump_46 assump_47 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          cases assump_47
          case intro assump_54 assump_55 =>
            cases assump_54
            case inl assump_56 =>
              cases assump_55
              case intro assump_60 assump_61 =>
                have assump_109 : (((p1 → False) → False) → ((p5 ∧ p1) → (False → p1))) := by
                  intro assump_69
                  intro assump_70
                  intro assump_71
                  apply False.elim assump_71
                let assump_68 := assump_43 assump_109
                apply False.elim assump_68
            case inr assump_57 =>
              cases assump_55
              case intro assump_79 assump_80 =>
                have assump_110 : (((p1 → False) → False) → ((p5 ∧ p1) → (False → p1))) := by
                  intro assump_88
                  intro assump_89
                  intro assump_90
                  apply False.elim assump_90
                let assump_87 := assump_43 assump_110
                apply False.elim assump_87
    case inr assump_45 =>
      have assump_111 : (((p1 → False) → False) → ((p5 ∧ p1) → (False → p1))) := by
        intro assump_101
        intro assump_102
        intro assump_103
        apply False.elim assump_103
      let assump_100 := assump_43 assump_111
      apply False.elim assump_100


variable (p7 p6 p5 p1 : Prop)
theorem file12_89881 : (((((p6 → False) → (False ∧ False)) → ((p5 ∧ False) → False)) ∧ (((p1 → False) → (p7 → p7)) → False)) → ((((p7 ∧ p6) → False) → ((True → False) ∧ (p1 ∨ True))) → False)) := by
  intro assump_11
  intro assump_12
  cases assump_11
  case intro assump_15 assump_16 =>
    have assump_31 : ((p1 → False) → (p7 → p7)) := by
      intro assump_22
      intro assump_23
      exact assump_23
    let assump_21 := assump_16 assump_31
    apply False.elim assump_21


variable (p6 p3 p1 p2 p0 : Prop)
theorem file12_90396 : ((((((p1 ∨ False) → (True ∨ p0)) ∨ ((False ∧ p6) → (False → p3))) ∨ (((p2 ∨ False) ∨ (False ∨ p3)) ∨ ((True → p2) ∧ (p6 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p1 ∨ False) → (True ∨ p0)) ∨ ((False ∧ p6) → (False → p3))) ∨ (((p2 ∨ False) ∨ (False ∨ p3)) ∨ ((True → p2) ∧ (p6 ∨ p2)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p7 p1 p3 p4 p2 p0 : Prop)
theorem file12_91042 : ((((((p7 ∨ p0) → False) ∨ ((False ∧ p1) ∨ (p1 ∧ p3))) → False) ∧ ((((p6 ∨ p4) ∧ (True → p2)) → ((False → False) ∨ (p7 → p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_31 : (((p6 ∨ p4) ∧ (True → p2)) → ((False → False) ∨ (p7 → p6))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inl
          intro assump_18
          apply False.elim assump_18
        case inr assump_13 =>
          apply Or.inl
          intro assump_25
          apply False.elim assump_25
    let assump_8 := assump_3 assump_31
    apply False.elim assump_8


variable (p6 p4 p3 p1 p5 : Prop)
theorem file12_91812 : ((((((True → False) → (p5 → p5)) → ((p3 → p1) → (p1 → False))) ∨ (((p3 → False) → (True → False)) → ((True ∧ p3) ∧ (p6 → p6)))) ∧ ((((p4 ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_36 : (((p4 ∨ True) → False) → False) := by
        intro assump_11
        have assump_37 : (p4 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_14 := assump_11 assump_37
        apply False.elim assump_14
      let assump_10 := assump_3 assump_36
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_38 : (((p4 ∨ True) → False) → False) := by
        intro assump_26
        have assump_39 : (p4 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_29 := assump_26 assump_39
        apply False.elim assump_29
      let assump_25 := assump_3 assump_38
      apply False.elim assump_25


variable (p1 p6 p5 p7 p3 p0 p4 : Prop)
theorem file12_92866 : ((((((p0 → False) → (p5 → p1)) → False) ∨ (((p7 → p6) ∨ (p3 ∨ p5)) → False)) ∧ ((((p7 ∨ p3) ∧ (p5 → p4)) ∨ ((True → False) ∧ (p5 → False))) ∧ (((p4 ∨ p6) → (False → False)) → False))) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_12
            case inl assump_14 =>
              have assump_114 : ((p4 ∨ p6) → (False → False)) := by
                intro assump_23
                intro assump_24
                apply False.elim assump_24
              let assump_22 := assump_9 assump_114
              apply False.elim assump_22
            case inr assump_15 =>
              have assump_115 : ((p4 ∨ p6) → (False → False)) := by
                intro assump_37
                intro assump_38
                apply False.elim assump_38
              let assump_36 := assump_9 assump_115
              apply False.elim assump_36
        case inr assump_11 =>
          cases assump_11
          case intro assump_44 assump_45 =>
            have assump_116 : ((p4 ∨ p6) → (False → False)) := by
              intro assump_53
              intro assump_54
              apply False.elim assump_54
            let assump_52 := assump_9 assump_116
            apply False.elim assump_52
    case inr assump_5 =>
      cases assump_3
      case intro assump_62 assump_63 =>
        cases assump_62
        case inl assump_64 =>
          cases assump_64
          case intro assump_66 assump_67 =>
            cases assump_66
            case inl assump_68 =>
              have assump_117 : ((p4 ∨ p6) → (False → False)) := by
                intro assump_77
                intro assump_78
                apply False.elim assump_78
              let assump_76 := assump_63 assump_117
              apply False.elim assump_76
            case inr assump_69 =>
              have assump_118 : ((p4 ∨ p6) → (False → False)) := by
                intro assump_91
                intro assump_92
                apply False.elim assump_92
              let assump_90 := assump_63 assump_118
              apply False.elim assump_90
        case inr assump_65 =>
          cases assump_65
          case intro assump_98 assump_99 =>
            have assump_119 : ((p4 ∨ p6) → (False → False)) := by
              intro assump_107
              intro assump_108
              apply False.elim assump_108
            let assump_106 := assump_63 assump_119
            apply False.elim assump_106


variable (p5 p1 p3 p4 p7 p6 : Prop)
theorem file12_95607 : ((((((p4 ∨ p6) ∧ (p1 ∧ p3)) → ((p6 ∧ p1) ∨ (p7 ∨ True))) ∨ (((p7 ∧ True) ∧ (p5 ∧ p6)) → ((False ∨ p3) ∧ (p5 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p4 ∨ p6) ∧ (p1 ∧ p3)) → ((p6 ∧ p1) ∨ (p7 ∨ True))) ∨ (((p7 ∧ True) ∧ (p5 ∧ p6)) → ((False ∨ p3) ∧ (p5 ∧ p5)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply Or.inr
          apply Or.inr
          apply True.intro
      case inr assump_9 =>
        cases assump_7
        case intro assump_20 assump_21 =>
          apply Or.inl
          apply And.intro
          exact assump_9
          exact assump_20
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p4 : Prop)
theorem file12_96484 : (((((p4 → False) → False) → ((False ∧ p4) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : (((p4 → False) → False) → ((False ∧ p4) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p0 p4 p7 p5 p6 p3 p1 : Prop)
theorem file12_96908 : (((((p4 ∨ False) → (p7 ∨ p0)) ∨ ((p1 → False) → False)) ∧ (((p1 → False) ∧ (False ∨ False)) ∨ ((p6 ∧ p5) ∨ (p3 ∨ True)))) → ((((True → p3) ∧ (p1 ∧ p2)) → False) → (((p1 ∧ p0) ∧ (p0 ∧ p5)) → ((p3 → p1) ∨ (p1 ∨ p0))))) := by
  intro assump_32
  intro assump_33
  intro assump_34
  cases assump_34
  case intro assump_35 assump_36 =>
    cases assump_35
    case intro assump_37 assump_38 =>
      cases assump_36
      case intro assump_43 assump_44 =>
        cases assump_32
        case intro assump_51 assump_52 =>
          cases assump_51
          case inl assump_53 =>
            cases assump_52
            case inl assump_57 =>
              cases assump_57
              case intro assump_59 assump_60 =>
                cases assump_60
                case inl assump_63 =>
                  apply False.elim assump_63
                case inr assump_64 =>
                  apply False.elim assump_64
            case inr assump_58 =>
              cases assump_58
              case inl assump_69 =>
                cases assump_69
                case intro assump_71 assump_72 =>
                  apply Or.inl
                  intro assump_77
                  exact assump_37
              case inr assump_70 =>
                cases assump_70
                case inl assump_80 =>
                  apply Or.inl
                  intro assump_84
                  exact assump_37
                case inr assump_81 =>
                  apply Or.inl
                  intro assump_89
                  exact assump_37
          case inr assump_54 =>
            cases assump_52
            case inl assump_94 =>
              cases assump_94
              case intro assump_96 assump_97 =>
                cases assump_97
                case inl assump_100 =>
                  apply False.elim assump_100
                case inr assump_101 =>
                  apply False.elim assump_101
            case inr assump_95 =>
              cases assump_95
              case inl assump_106 =>
                cases assump_106
                case intro assump_108 assump_109 =>
                  apply Or.inl
                  intro assump_114
                  exact assump_37
              case inr assump_107 =>
                cases assump_107
                case inl assump_117 =>
                  apply Or.inl
                  intro assump_121
                  exact assump_37
                case inr assump_118 =>
                  apply Or.inl
                  intro assump_126
                  exact assump_37


variable (p7 p6 p2 p5 p0 : Prop)
theorem file12_99509 : ((((((p7 ∨ p5) ∨ (p5 ∧ p2)) → False) → (((p6 ∨ p6) ∨ (p0 ∧ p7)) ∨ ((p7 → False) ∧ (True ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p7 ∨ p5) ∨ (p5 ∧ p2)) → False) → (((p6 ∨ p6) ∨ (p0 ∧ p7)) ∨ ((p7 → False) ∧ (True ∨ p5)))) := by
    intro assump_5
    apply Or.inr
    apply And.intro
    intro assump_8
    have assump_20 : ((p7 ∨ p5) ∨ (p5 ∧ p2)) := by
      apply Or.inl
      apply Or.inl
      exact assump_8
    let assump_12 := assump_5 assump_20
    apply False.elim assump_12
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p3 p5 p7 : Prop)
theorem file12_100180 : (((((True ∨ p7) ∨ (False ∨ False)) ∧ ((p5 → p4) → (False → p3))) → False) → False) := by
  intro assump_10
  have assump_21 : (((True ∨ p7) ∨ (False ∨ False)) ∧ ((p5 → p4) → (False → p3))) := by
    apply And.intro
    apply Or.inl
    apply Or.inl
    apply True.intro
    intro assump_14
    intro assump_15
    apply False.elim assump_15
  let assump_13 := assump_10 assump_21
  apply False.elim assump_13


variable (p4 p7 p1 p2 p3 p6 : Prop)
theorem file12_100649 : ((((((p6 ∧ False) ∧ (True → p4)) ∧ ((p1 → False) ∧ (p7 ∧ p1))) → (((True → p2) → (p6 ∧ p3)) → ((p4 → p2) ∧ (p1 → True)))) → ((((p2 ∨ p2) → (p3 → p6)) → ((False ∧ p6) ∨ (False → True))) → False)) → False) := by
  intro assump_12
  have assump_42 : ((((p6 ∧ False) ∧ (True → p4)) ∧ ((p1 → False) ∧ (p7 ∧ p1))) → (((True → p2) → (p6 ∧ p3)) → ((p4 → p2) ∧ (p1 → True)))) := by
    intro assump_16
    intro assump_17
    apply And.intro
    intro assump_18
    cases assump_16
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          apply False.elim assump_28
    intro assump_33
    apply True.intro
  let assump_15 := assump_12 assump_42
  have assump_43 : (((p2 ∨ p2) → (p3 → p6)) → ((False ∧ p6) ∨ (False → True))) := by
    intro assump_35
    apply Or.inr
    intro assump_38
    apply True.intro
  let assump_34 := assump_15 assump_43
  apply False.elim assump_34


variable (p1 p0 p6 p2 p3 p7 p5 p4 : Prop)
theorem file12_101702 : (((((True → False) → (p0 ∧ p4)) → ((p5 ∨ p5) ∧ (p3 → p6))) → False) → ((((False → False) → False) → ((p0 ∧ p7) ∨ (p4 ∧ p1))) ∨ (((p2 ∧ p3) ∨ (p4 → False)) → False))) := by
  intro assump_14
  apply Or.inl
  intro assump_17
  have assump_27 : (False → False) := by
    intro assump_21
    apply False.elim assump_21
  let assump_20 := assump_17 assump_27
  apply False.elim assump_20


variable (p1 p7 p5 p4 p2 p0 p6 p3 : Prop)
theorem file12_102151 : (((((p4 ∧ False) ∧ (p2 → p3)) ∨ ((p3 → True) → (p3 → False))) ∧ (((False ∧ p3) → (True ∨ p3)) ∨ ((False → p5) ∨ (p1 ∨ p5)))) → ((((True ∧ p7) ∧ (p7 → False)) → ((False ∨ p6) → False)) ∨ (((p4 ∨ p7) → (p0 → False)) ∨ ((True → p7) ∨ (p7 ∧ True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9
    case inr assump_5 =>
      cases assump_3
      case inl assump_16 =>
        apply Or.inl
        intro assump_20
        intro assump_21
        cases assump_21
        case inl assump_22 =>
          apply False.elim assump_22
        case inr assump_23 =>
          cases assump_20
          case intro assump_28 assump_29 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              have assump_118 : p7 := by
                exact assump_31
              let assump_38 := assump_29 assump_118
              apply False.elim assump_38
      case inr assump_17 =>
        cases assump_17
        case inl assump_42 =>
          apply Or.inl
          intro assump_46
          intro assump_47
          cases assump_47
          case inl assump_48 =>
            apply False.elim assump_48
          case inr assump_49 =>
            cases assump_46
            case intro assump_54 assump_55 =>
              cases assump_54
              case intro assump_56 assump_57 =>
                have assump_119 : p7 := by
                  exact assump_57
                let assump_64 := assump_55 assump_119
                apply False.elim assump_64
        case inr assump_43 =>
          cases assump_43
          case inl assump_68 =>
            apply Or.inl
            intro assump_72
            intro assump_73
            cases assump_73
            case inl assump_74 =>
              apply False.elim assump_74
            case inr assump_75 =>
              cases assump_72
              case intro assump_80 assump_81 =>
                cases assump_80
                case intro assump_82 assump_83 =>
                  have assump_120 : p7 := by
                    exact assump_83
                  let assump_90 := assump_81 assump_120
                  apply False.elim assump_90
          case inr assump_69 =>
            apply Or.inl
            intro assump_96
            intro assump_97
            cases assump_97
            case inl assump_98 =>
              apply False.elim assump_98
            case inr assump_99 =>
              cases assump_96
              case intro assump_104 assump_105 =>
                cases assump_104
                case intro assump_106 assump_107 =>
                  have assump_121 : p7 := by
                    exact assump_107
                  let assump_114 := assump_105 assump_121
                  apply False.elim assump_114


variable (p6 p3 : Prop)
theorem file12_105157 : ((((((p6 ∧ p3) ∨ (False ∨ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p6 ∧ p3) ∨ (False ∨ True)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p6 ∧ p3) ∨ (False ∨ True)) := by
      apply Or.inr
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p5 p4 p0 p7 p6 p1 : Prop)
theorem file12_105656 : (((((True ∨ p0) → False) → ((p0 → p6) ∨ (False → p2))) ∨ (((p2 → False) ∨ (p2 ∨ p1)) → False)) ∨ ((((False → p2) → (p5 ∧ p4)) ∧ ((p4 ∨ p5) → (p7 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_12 : (True ∨ p0) := by
    apply Or.inl
    apply True.intro
  let assump_8 := assump_1 assump_12
  apply False.elim assump_8


variable (p1 p6 p5 p4 p0 p2 p3 : Prop)
theorem file12_106110 : (((((p2 → p6) ∧ (p0 ∧ p6)) ∨ ((False → p0) ∧ (p0 → p6))) → False) → ((((p0 → p3) ∨ (p4 ∧ p1)) ∧ ((p0 → False) ∧ (p6 ∧ p5))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_10
        case intro assump_13 assump_14 =>
          have assump_65 : (((p2 → p6) ∧ (p0 ∧ p6)) ∨ ((False → p0) ∧ (p0 → p6))) := by
            apply Or.inr
            apply And.intro
            intro assump_25
            apply False.elim assump_25
            intro assump_28
            exact assump_13
          let assump_21 := assump_1 assump_65
          apply False.elim assump_21
    case inr assump_6 =>
      cases assump_6
      case intro assump_34 assump_35 =>
        cases assump_4
        case intro assump_40 assump_41 =>
          cases assump_41
          case intro assump_44 assump_45 =>
            have assump_66 : (((p2 → p6) ∧ (p0 ∧ p6)) ∨ ((False → p0) ∧ (p0 → p6))) := by
              apply Or.inr
              apply And.intro
              intro assump_56
              apply False.elim assump_56
              intro assump_59
              exact assump_44
            let assump_52 := assump_1 assump_66
            apply False.elim assump_52


variable (p4 p2 p0 p5 p7 p3 : Prop)
theorem file12_107498 : ((((((p5 → False) → (p2 → True)) → ((True → p0) → (False → False))) → False) ∨ ((((p3 → False) ∧ (False ∧ p4)) ∧ ((True ∨ False) ∧ (p5 → False))) ∧ (((p7 ∧ False) ∨ (p0 → p4)) ∨ ((p3 ∧ p7) → (True → p7))))) → False) := by
  intro assump_16
  cases assump_16
  case inl assump_17 =>
    have assump_42 : (((p5 → False) → (p2 → True)) → ((True → p0) → (False → False))) := by
      intro assump_22
      intro assump_23
      intro assump_24
      apply False.elim assump_24
    let assump_21 := assump_17 assump_42
    apply False.elim assump_21
  case inr assump_18 =>
    cases assump_18
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          cases assump_35
          case intro assump_38 assump_39 =>
            apply False.elim assump_38


variable (p6 p1 p5 p0 p2 p4 p3 p7 : Prop)
theorem file12_108428 : ((((((False ∧ p0) ∨ (False ∧ False)) ∧ ((p1 → p2) ∧ (p5 ∨ p2))) → (((p6 → p3) → (p1 ∧ p1)) ∧ ((p4 ∧ p3) ∧ (p7 → p6)))) → False) → False) := by
  intro assump_1
  have assump_77 : ((((False ∧ p0) ∨ (False ∧ False)) ∧ ((p1 → p2) ∧ (p5 ∨ p2))) → (((p6 → p3) → (p1 ∧ p1)) ∧ ((p4 ∧ p3) ∧ (p7 → p6)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    apply And.intro
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
      case inr assump_12 =>
        cases assump_12
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
    cases assump_5
    case intro assump_23 assump_24 =>
      cases assump_23
      case inl assump_25 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          apply False.elim assump_27
      case inr assump_26 =>
        cases assump_26
        case intro assump_31 assump_32 =>
          apply False.elim assump_31
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_35 assump_36 =>
      cases assump_35
      case inl assump_37 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          apply False.elim assump_39
      case inr assump_38 =>
        cases assump_38
        case intro assump_43 assump_44 =>
          apply False.elim assump_43
    cases assump_5
    case intro assump_47 assump_48 =>
      cases assump_47
      case inl assump_49 =>
        cases assump_49
        case intro assump_51 assump_52 =>
          apply False.elim assump_51
      case inr assump_50 =>
        cases assump_50
        case intro assump_55 assump_56 =>
          apply False.elim assump_55
    intro assump_59
    cases assump_5
    case intro assump_62 assump_63 =>
      cases assump_62
      case inl assump_64 =>
        cases assump_64
        case intro assump_66 assump_67 =>
          apply False.elim assump_66
      case inr assump_65 =>
        cases assump_65
        case intro assump_70 assump_71 =>
          apply False.elim assump_70
  let assump_4 := assump_1 assump_77
  apply False.elim assump_4


variable (p3 p5 p6 p7 p0 p2 p1 : Prop)
theorem file12_110699 : ((((((p5 → False) → False) → False) ∧ (((p1 → p6) ∧ (False ∨ p3)) ∧ ((p0 → False) ∧ (True ∧ False)))) ∧ ((((p3 → p7) ∧ (False ∨ False)) → ((p5 ∨ p7) → (p6 ∨ p0))) ∧ (((p2 ∨ p6) → (p5 → p7)) → False))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_19
          case inl assump_22 =>
            apply False.elim assump_22
          case inr assump_23 =>
            cases assump_17
            case intro assump_28 assump_29 =>
              cases assump_29
              case intro assump_32 assump_33 =>
                apply False.elim assump_33


variable (p7 p0 p2 p3 : Prop)
theorem file12_111549 : (((((p7 → p2) → (p0 ∧ p2)) → ((False → False) ∧ (True ∨ p3))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p7 → p2) → (p0 ∧ p2)) → ((False → False) ∧ (True ∨ p3))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    apply False.elim assump_6
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p4 p7 p2 p3 p1 p0 p6 p5 : Prop)
theorem file12_111994 : (((((False ∧ p4) ∨ (p2 → False)) → ((p0 → p3) → (p2 → False))) → (((p3 ∨ p7) ∨ (p3 ∨ True)) → ((p5 → False) ∧ (p3 → False)))) → ((((p6 ∨ p0) ∧ (p1 ∨ p2)) → ((False → p2) ∨ (False ∨ False))) ∧ (((p7 → True) → (p3 → p4)) ∨ ((p2 ∧ p1) ∧ (p7 ∧ p6))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case inl assump_9 =>
        apply Or.inl
        intro assump_15
        apply False.elim assump_15
      case inr assump_10 =>
        apply Or.inl
        intro assump_22
        apply False.elim assump_22
    case inr assump_6 =>
      cases assump_4
      case inl assump_27 =>
        apply Or.inl
        intro assump_33
        apply False.elim assump_33
      case inr assump_28 =>
        apply Or.inl
        intro assump_40
        apply False.elim assump_40
  apply Or.inl
  intro assump_45
  intro assump_46
  have assump_80 : (((False ∧ p4) ∨ (p2 → False)) → ((p0 → p3) → (p2 → False))) := by
    intro assump_54
    intro assump_55
    intro assump_56
    cases assump_54
    case inl assump_61 =>
      cases assump_61
      case intro assump_63 assump_64 =>
        apply False.elim assump_63
    case inr assump_62 =>
      have assump_81 : p2 := by
        exact assump_56
      let assump_69 := assump_62 assump_81
      apply False.elim assump_69
  let assump_53 := assump_1 assump_80
  have assump_82 : ((p3 ∨ p7) ∨ (p3 ∨ True)) := by
    apply Or.inl
    apply Or.inl
    exact assump_46
  let assump_73 := assump_53 assump_82
  let assump_74 := And.right assump_73
  have assump_83 : p3 := by
    exact assump_46
  let assump_76 := assump_74 assump_83
  apply False.elim assump_76


variable (p7 p0 p5 p1 p2 p4 p3 : Prop)
theorem file12_113791 : ((((((p4 → p3) → (p2 → p0)) → False) → (((True ∧ False) → (p7 ∧ True)) ∨ ((p1 ∨ p2) → (False → p5)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 → p3) → (p2 → p0)) → False) → (((True ∧ False) → (p7 ∧ True)) ∨ ((p1 ∨ p2) → (False → p5)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply And.intro
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
    apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p5 p0 p6 p1 p3 p2 p4 : Prop)
theorem file12_114375 : (((((False → False) → False) ∧ ((p1 → False) ∨ (p2 → p2))) → False) ∨ ((((p4 ∨ p7) → (p6 ∨ p1)) ∧ ((p1 ∧ p3) → False)) ∧ (((True → p0) ∨ (p7 → False)) ∧ ((p2 ∨ p5) ∧ (p1 → p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_28 : (False → False) := by
        intro assump_12
        apply False.elim assump_12
      let assump_11 := assump_2 assump_28
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_29 : (False → False) := by
        intro assump_22
        apply False.elim assump_22
      let assump_21 := assump_2 assump_29
      apply False.elim assump_21


variable (p2 p4 : Prop)
theorem file12_115119 : ((((((True → False) ∧ (p4 → True)) → False) ∨ (((False → False) → False) → ((p2 ∧ False) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((True → False) ∧ (p4 → True)) → False) ∨ (((False → False) → False) → ((p2 ∧ False) ∨ (False → False)))) := by
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


variable (p4 p0 p5 p7 p3 p2 p1 : Prop)
theorem file12_115756 : ((((((p1 → False) → False) → False) ∨ (((p3 ∨ p3) ∧ (False ∨ p7)) → ((p5 ∨ True) → False))) ∧ ((((p4 → False) → (p0 → False)) ∧ ((False ∧ p4) → False)) ∧ (((p4 → p4) → False) ∧ ((True ∨ p1) ∨ (p2 ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_17
            case inl assump_20 =>
              cases assump_20
              case inl assump_22 =>
                have assump_124 : (p4 → p4) := by
                  intro assump_27
                  exact assump_27
                let assump_26 := assump_16 assump_124
                apply False.elim assump_26
              case inr assump_23 =>
                have assump_125 : (p4 → p4) := by
                  intro assump_37
                  exact assump_37
                let assump_36 := assump_16 assump_125
                apply False.elim assump_36
            case inr assump_21 =>
              cases assump_21
              case inl assump_43 =>
                have assump_126 : (p4 → p4) := by
                  intro assump_49
                  exact assump_49
                let assump_48 := assump_16 assump_126
                apply False.elim assump_48
              case inr assump_44 =>
                have assump_127 : (p4 → p4) := by
                  intro assump_59
                  exact assump_59
                let assump_58 := assump_16 assump_127
                apply False.elim assump_58
    case inr assump_5 =>
      cases assump_3
      case intro assump_67 assump_68 =>
        cases assump_67
        case intro assump_69 assump_70 =>
          cases assump_68
          case intro assump_75 assump_76 =>
            cases assump_76
            case inl assump_79 =>
              cases assump_79
              case inl assump_81 =>
                have assump_128 : (p4 → p4) := by
                  intro assump_86
                  exact assump_86
                let assump_85 := assump_75 assump_128
                apply False.elim assump_85
              case inr assump_82 =>
                have assump_129 : (p4 → p4) := by
                  intro assump_96
                  exact assump_96
                let assump_95 := assump_75 assump_129
                apply False.elim assump_95
            case inr assump_80 =>
              cases assump_80
              case inl assump_102 =>
                have assump_130 : (p4 → p4) := by
                  intro assump_108
                  exact assump_108
                let assump_107 := assump_75 assump_130
                apply False.elim assump_107
              case inr assump_103 =>
                have assump_131 : (p4 → p4) := by
                  intro assump_118
                  exact assump_118
                let assump_117 := assump_75 assump_131
                apply False.elim assump_117


variable (p1 p0 p7 p2 p5 p6 p3 p4 : Prop)
theorem file12_118900 : (((((False → p5) ∨ (p0 → False)) ∨ ((p7 → p5) → False)) ∨ (((p1 ∧ p4) → False) ∧ ((p2 → False) ∧ (p6 → p1)))) ∨ ((((p0 → False) → False) ∨ ((True ∧ p2) ∨ (False → False))) ∧ (((p7 → p1) → (p3 → p0)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p1 p2 p0 p5 p7 p6 : Prop)
theorem file12_119281 : (((((p0 ∧ p5) ∨ (p5 ∨ p5)) ∨ ((p0 ∨ p6) → (p0 → p1))) ∨ (((True → False) ∧ (p7 → False)) ∧ ((p0 ∨ p7) → (p0 ∨ p5)))) → ((((p7 → True) → False) ∧ ((p5 ∧ p2) ∧ (p2 ∧ p1))) → (((False → False) → (p0 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          cases assump_1
          case inl assump_24 =>
            cases assump_24
            case inl assump_26 =>
              cases assump_26
              case inl assump_28 =>
                cases assump_28
                case intro assump_30 assump_31 =>
                  have assump_101 : (p7 → True) := by
                    intro assump_43
                    apply True.intro
                  let assump_42 := assump_6 assump_101
                  apply False.elim assump_42
              case inr assump_29 =>
                cases assump_29
                case inl assump_47 =>
                  have assump_102 : (p7 → True) := by
                    intro assump_57
                    apply True.intro
                  let assump_56 := assump_6 assump_102
                  apply False.elim assump_56
                case inr assump_48 =>
                  have assump_103 : (p7 → True) := by
                    intro assump_69
                    apply True.intro
                  let assump_68 := assump_6 assump_103
                  apply False.elim assump_68
            case inr assump_27 =>
              have assump_104 : (p7 → True) := by
                intro assump_81
                apply True.intro
              let assump_80 := assump_6 assump_104
              apply False.elim assump_80
          case inr assump_25 =>
            cases assump_25
            case intro assump_85 assump_86 =>
              cases assump_85
              case intro assump_87 assump_88 =>
                have assump_105 : True := by
                  apply True.intro
                let assump_97 := assump_87 assump_105
                apply False.elim assump_97


variable (p3 p2 : Prop)
theorem file12_121533 : ((((((p2 → False) → False) ∧ ((p3 → p3) → False)) → False) → False) → False) := by
  intro assump_15
  have assump_36 : ((((p2 → False) → False) ∧ ((p3 → p3) → False)) → False) := by
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      have assump_37 : (p3 → p3) := by
        intro assump_27
        exact assump_27
      let assump_26 := assump_21 assump_37
      apply False.elim assump_26
  let assump_18 := assump_15 assump_36
  apply False.elim assump_18


variable (p6 p5 p7 p0 : Prop)
theorem file12_122079 : ((((((p0 ∧ p5) ∨ (True ∧ p7)) ∧ ((True → False) ∧ (p6 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_45 : ((((p0 ∧ p5) ∨ (True ∧ p7)) ∧ ((True → False) ∧ (p6 ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
      case inr assump_9 =>
        cases assump_9
        case intro assump_26 assump_27 =>
          cases assump_7
          case intro assump_32 assump_33 =>
            cases assump_33
            case intro assump_36 assump_37 =>
              apply False.elim assump_37
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


variable (p1 p2 p6 p3 p5 p7 : Prop)
theorem file12_123063 : (((((p1 → False) → (False → p6)) ∧ ((False ∧ p3) ∧ (True ∧ False))) → False) ∨ ((((p7 ∨ p6) → False) → False) ∨ (((False → p7) → False) → ((p5 → False) → (p7 → p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8


