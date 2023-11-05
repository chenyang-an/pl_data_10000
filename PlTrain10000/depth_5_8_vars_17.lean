variable (p6 p7 p3 p2 p5 p0 p1 : Prop)
theorem file17_47 : (((((False ∧ p3) → False) → ((p5 → False) → (p6 ∧ p3))) ∧ (((p2 ∨ p7) → (p2 ∨ p1)) → False)) → ((((p0 ∨ p5) → False) → ((False → p0) → (p1 → False))) ∧ (((p5 → False) → False) → ((p2 ∧ p3) → False)))) := by
  intro assump_9
  apply And.intro
  intro assump_10
  intro assump_11
  intro assump_12
  cases assump_9
  case intro assump_19 assump_20 =>
    have assump_63 : ((p2 ∨ p7) → (p2 ∨ p1)) := by
      intro assump_26
      cases assump_26
      case inl assump_27 =>
        apply Or.inl
        exact assump_27
      case inr assump_28 =>
        apply Or.inr
        exact assump_12
    let assump_25 := assump_20 assump_63
    apply False.elim assump_25
  intro assump_36
  intro assump_37
  cases assump_37
  case intro assump_38 assump_39 =>
    cases assump_9
    case intro assump_46 assump_47 =>
      have assump_64 : ((p2 ∨ p7) → (p2 ∨ p1)) := by
        intro assump_53
        cases assump_53
        case inl assump_54 =>
          apply Or.inl
          exact assump_54
        case inr assump_55 =>
          apply Or.inl
          exact assump_38
      let assump_52 := assump_47 assump_64
      apply False.elim assump_52


variable (p0 p2 p3 p5 p4 : Prop)
theorem file17_1248 : ((((((False ∧ p5) ∧ (p3 → True)) ∧ ((False → False) ∧ (False → p2))) → False) ∧ ((((p0 → False) ∧ (True → False)) → ((p4 → True) → False)) → False)) → False) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    have assump_38 : (((p0 → False) ∧ (True → False)) → ((p4 → True) → False)) := by
      intro assump_21
      intro assump_22
      cases assump_21
      case intro assump_25 assump_26 =>
        have assump_39 : True := by
          apply True.intro
        let assump_31 := assump_26 assump_39
        apply False.elim assump_31
    let assump_20 := assump_15 assump_38
    apply False.elim assump_20


variable (p2 p0 p4 p5 p1 p3 p7 : Prop)
theorem file17_1953 : (((((p4 ∧ p3) → (False → False)) ∨ ((False ∨ p0) → (p7 ∧ p2))) ∧ (((True ∧ True) ∨ (p1 ∧ p0)) ∨ ((p4 → False) → (p7 ∨ False)))) → ((((p3 → False) ∧ (p7 → False)) → ((p7 → p3) ∨ (p1 → False))) ∨ (((p5 ∧ p2) ∨ (p0 ∨ p1)) ∧ ((True → p7) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply Or.inl
            intro assump_18
            cases assump_18
            case intro assump_19 assump_20 =>
              apply Or.inl
              intro assump_25
              have assump_136 : p7 := by
                exact assump_25
              let assump_29 := assump_20 assump_136
              apply False.elim assump_29
        case inr assump_11 =>
          cases assump_11
          case intro assump_33 assump_34 =>
            apply Or.inl
            intro assump_39
            cases assump_39
            case intro assump_40 assump_41 =>
              apply Or.inl
              intro assump_46
              have assump_137 : p7 := by
                exact assump_46
              let assump_50 := assump_41 assump_137
              apply False.elim assump_50
      case inr assump_9 =>
        apply Or.inl
        intro assump_56
        cases assump_56
        case intro assump_57 assump_58 =>
          apply Or.inl
          intro assump_63
          have assump_138 : p7 := by
            exact assump_63
          let assump_67 := assump_58 assump_138
          apply False.elim assump_67
    case inr assump_5 =>
      cases assump_3
      case inl assump_73 =>
        cases assump_73
        case inl assump_75 =>
          cases assump_75
          case intro assump_77 assump_78 =>
            apply Or.inl
            intro assump_83
            cases assump_83
            case intro assump_84 assump_85 =>
              apply Or.inl
              intro assump_90
              have assump_139 : p7 := by
                exact assump_90
              let assump_94 := assump_85 assump_139
              apply False.elim assump_94
        case inr assump_76 =>
          cases assump_76
          case intro assump_98 assump_99 =>
            apply Or.inl
            intro assump_104
            cases assump_104
            case intro assump_105 assump_106 =>
              apply Or.inl
              intro assump_111
              have assump_140 : p7 := by
                exact assump_111
              let assump_115 := assump_106 assump_140
              apply False.elim assump_115
      case inr assump_74 =>
        apply Or.inl
        intro assump_121
        cases assump_121
        case intro assump_122 assump_123 =>
          apply Or.inl
          intro assump_128
          have assump_141 : p7 := by
            exact assump_128
          let assump_132 := assump_123 assump_141
          apply False.elim assump_132


variable (p2 p4 p7 p1 p5 p3 : Prop)
theorem file17_5039 : (((((p3 → False) ∧ (True → False)) → ((True → False) → (p1 → False))) → False) → ((((p5 → p2) → (True ∨ p2)) → False) → (((p3 → False) → (p3 → False)) ∧ ((p4 → False) ∧ (p7 → p2))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  have assump_90 : (((p3 → False) ∧ (True → False)) → ((True → False) → (p1 → False))) := by
    intro assump_14
    intro assump_15
    intro assump_16
    cases assump_14
    case intro assump_21 assump_22 =>
      have assump_91 : True := by
        apply True.intro
      let assump_27 := assump_22 assump_91
      apply False.elim assump_27
  let assump_13 := assump_1 assump_90
  apply False.elim assump_13
  apply And.intro
  intro assump_34
  have assump_92 : (((p3 → False) ∧ (True → False)) → ((True → False) → (p1 → False))) := by
    intro assump_42
    intro assump_43
    intro assump_44
    cases assump_42
    case intro assump_49 assump_50 =>
      have assump_93 : True := by
        apply True.intro
      let assump_55 := assump_50 assump_93
      apply False.elim assump_55
  let assump_41 := assump_1 assump_92
  apply False.elim assump_41
  intro assump_62
  have assump_94 : (((p3 → False) ∧ (True → False)) → ((True → False) → (p1 → False))) := by
    intro assump_70
    intro assump_71
    intro assump_72
    cases assump_70
    case intro assump_77 assump_78 =>
      have assump_95 : True := by
        apply True.intro
      let assump_83 := assump_78 assump_95
      apply False.elim assump_83
  let assump_69 := assump_1 assump_94
  apply False.elim assump_69


variable (p1 p7 p4 p5 : Prop)
theorem file17_6661 : ((((((True → False) → (p5 → p4)) → ((p1 ∧ p5) → (p1 → p1))) ∨ (((p7 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_21 : ((((True → False) → (p5 → p4)) → ((p1 ∧ p5) → (p1 → p1))) ∨ (((p7 → False) → False) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      exact assump_10
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p3 p0 p4 p2 p5 p1 p6 : Prop)
theorem file17_7201 : (((((p1 → False) ∧ (p3 → False)) ∧ ((p7 → False) ∧ (p6 → False))) ∧ (((p6 → p7) ∧ (p7 ∨ p1)) ∧ ((p2 ∧ p5) ∧ (p0 ∧ p7)))) → ((((p3 ∨ p6) → (p0 ∨ True)) → ((p5 ∧ False) ∨ (False ∧ p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          cases assump_6
          case intro assump_21 assump_22 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              cases assump_24
              case inl assump_27 =>
                cases assump_22
                case intro assump_31 assump_32 =>
                  cases assump_31
                  case intro assump_33 assump_34 =>
                    cases assump_32
                    case intro assump_39 assump_40 =>
                      have assump_83 : p7 := by
                        exact assump_40
                      let assump_52 := assump_15 assump_83
                      apply False.elim assump_52
              case inr assump_28 =>
                cases assump_22
                case intro assump_58 assump_59 =>
                  cases assump_58
                  case intro assump_60 assump_61 =>
                    cases assump_59
                    case intro assump_66 assump_67 =>
                      have assump_84 : p7 := by
                        exact assump_67
                      let assump_79 := assump_15 assump_84
                      apply False.elim assump_79


variable (p5 p7 p2 p1 p3 p4 : Prop)
theorem file17_8879 : (((((p7 ∧ False) ∧ (True ∧ p5)) ∧ ((p4 → p5) → (p3 → p4))) ∧ (((p1 → False) → (p2 → False)) ∧ ((p7 → p4) ∧ (True → p5)))) → False) := by
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


variable (p5 p7 p4 p0 p6 p1 p2 : Prop)
theorem file17_9360 : ((((((p5 → True) ∧ (p7 → False)) → False) ∨ (((True → p4) ∨ (p0 ∧ p6)) → False)) ∧ ((((False ∧ True) ∧ (p1 → p2)) → ((False ∨ p4) → (p7 → False))) → False)) → False) := by
  intro assump_33
  cases assump_33
  case intro assump_34 assump_35 =>
    cases assump_34
    case inl assump_36 =>
      have assump_88 : (((False ∧ True) ∧ (p1 → p2)) → ((False ∨ p4) → (p7 → False))) := by
        intro assump_43
        intro assump_44
        intro assump_45
        cases assump_44
        case inl assump_48 =>
          apply False.elim assump_48
        case inr assump_49 =>
          cases assump_43
          case intro assump_54 assump_55 =>
            cases assump_54
            case intro assump_56 assump_57 =>
              apply False.elim assump_56
      let assump_42 := assump_35 assump_88
      apply False.elim assump_42
    case inr assump_37 =>
      have assump_89 : (((False ∧ True) ∧ (p1 → p2)) → ((False ∨ p4) → (p7 → False))) := by
        intro assump_68
        intro assump_69
        intro assump_70
        cases assump_69
        case inl assump_73 =>
          apply False.elim assump_73
        case inr assump_74 =>
          cases assump_68
          case intro assump_79 assump_80 =>
            cases assump_79
            case intro assump_81 assump_82 =>
              apply False.elim assump_81
      let assump_67 := assump_35 assump_89
      apply False.elim assump_67


variable (p0 p3 p2 p1 p7 p6 p4 : Prop)
theorem file17_10831 : (((((p1 → p2) → (False → p2)) ∨ ((p2 → p6) ∧ (p3 → False))) → (((p4 ∨ True) ∨ (p0 → False)) ∧ ((False → False) ∨ (True ∨ p0)))) ∨ ((((p3 ∧ p4) → False) → ((p7 → False) ∨ (p7 ∧ p3))) ∧ (((p3 → False) → (p6 → p1)) ∨ ((True → p0) → False)))) := by
  apply Or.inl
  intro assump_9
  apply And.intro
  cases assump_9
  case inl assump_10 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
  cases assump_9
  case inl assump_20 =>
    apply Or.inl
    intro assump_24
    apply False.elim assump_24
  case inr assump_21 =>
    cases assump_21
    case intro assump_27 assump_28 =>
      apply Or.inl
      intro assump_33
      apply False.elim assump_33


variable (p4 p0 p3 p6 p1 p5 : Prop)
theorem file17_11690 : ((((((p5 → p0) ∧ (p6 ∧ p3)) → False) → (((p1 → False) ∨ (p4 → False)) → ((False ∧ True) ∨ (False → p3)))) → False) → False) := by
  intro assump_42
  have assump_67 : ((((p5 → p0) ∧ (p6 ∧ p3)) → False) → (((p1 → False) ∨ (p4 → False)) → ((False ∧ True) ∨ (False → p3)))) := by
    intro assump_46
    intro assump_47
    cases assump_47
    case inl assump_48 =>
      apply Or.inr
      intro assump_54
      apply False.elim assump_54
    case inr assump_49 =>
      apply Or.inr
      intro assump_61
      apply False.elim assump_61
  let assump_45 := assump_42 assump_67
  apply False.elim assump_45


variable (p4 p7 p6 p0 p3 p2 : Prop)
theorem file17_12355 : (((((p4 ∨ p6) → (p3 → p3)) ∨ ((p2 → False) → (p6 → p2))) → False) → ((((True ∧ p0) ∧ (p4 ∨ p7)) → ((p2 → False) → (p7 → False))) → (((False ∨ False) → False) ∨ ((True → False) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    apply False.elim assump_8
  case inr assump_9 =>
    apply False.elim assump_9


variable (p4 p2 p6 p5 : Prop)
theorem file17_12792 : ((((((p6 ∧ p4) → False) → ((p4 ∧ p5) → False)) → (((p2 → False) ∧ (False → False)) → ((p4 → p6) → (False → p2)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p6 ∧ p4) → False) → ((p4 ∧ p5) → False)) → (((p2 → False) ∧ (False → False)) → ((p4 → p6) → (False → p2)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p0 p1 p7 p4 p2 : Prop)
theorem file17_13315 : ((((((p1 → p0) → False) ∧ ((True ∧ p7) ∧ (p2 → p0))) ∧ (((p4 → False) ∧ (p6 ∨ p0)) → ((p7 ∧ p0) ∧ (True ∨ p4)))) ∧ ((((True ∧ False) → False) → ((False ∧ False) → False)) ∧ (((p6 ∨ p7) ∨ (p6 ∧ True)) ∧ ((p4 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_22 assump_23 =>
              cases assump_23
              case intro assump_26 assump_27 =>
                cases assump_26
                case inl assump_28 =>
                  cases assump_28
                  case inl assump_30 =>
                    have assump_63 : (p4 → True) := by
                      intro assump_37
                      apply True.intro
                    let assump_36 := assump_27 assump_63
                    apply False.elim assump_36
                  case inr assump_31 =>
                    have assump_64 : (p4 → True) := by
                      intro assump_46
                      apply True.intro
                    let assump_45 := assump_27 assump_64
                    apply False.elim assump_45
                case inr assump_29 =>
                  cases assump_29
                  case intro assump_50 assump_51 =>
                    have assump_65 : (p4 → True) := by
                      intro assump_59
                      apply True.intro
                    let assump_58 := assump_27 assump_65
                    apply False.elim assump_58


variable (p1 p6 p5 p4 p7 p2 : Prop)
theorem file17_15101 : ((((((p4 ∧ p6) → (False → p5)) → False) → (((p6 ∨ p2) ∨ (p7 ∨ p4)) ∧ ((p1 → False) → (p6 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p4 ∧ p6) → (False → p5)) → False) → (((p6 ∨ p2) ∨ (p7 ∨ p4)) ∧ ((p1 → False) → (p6 ∧ p1)))) := by
    intro assump_5
    apply And.intro
    have assump_45 : ((p4 ∧ p6) → (False → p5)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_45
    apply False.elim assump_8
    intro assump_16
    apply And.intro
    have assump_46 : ((p4 ∧ p6) → (False → p5)) := by
      intro assump_22
      intro assump_23
      apply False.elim assump_23
    let assump_21 := assump_5 assump_46
    apply False.elim assump_21
    have assump_47 : ((p4 ∧ p6) → (False → p5)) := by
      intro assump_34
      intro assump_35
      apply False.elim assump_35
    let assump_33 := assump_5 assump_47
    apply False.elim assump_33
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p2 p6 p7 p0 p4 p5 : Prop)
theorem file17_16168 : ((((((p2 → False) ∧ (p0 ∧ False)) → ((p5 ∧ p5) → (p6 → p6))) ∨ (((p4 ∨ True) ∧ (p5 ∧ p7)) ∧ ((p2 ∨ p5) ∧ (p4 → False)))) → False) → False) := by
  intro assump_5
  have assump_33 : ((((p2 → False) ∧ (p0 ∧ False)) → ((p5 ∧ p5) → (p6 → p6))) ∨ (((p4 ∨ True) ∧ (p5 ∧ p7)) ∧ ((p2 ∨ p5) ∧ (p4 → False)))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_10
    case intro assump_14 assump_15 =>
      cases assump_9
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          apply False.elim assump_25
  let assump_8 := assump_5 assump_33
  apply False.elim assump_8


variable (p4 p5 p1 p0 p2 : Prop)
theorem file17_16894 : (((((False → p4) → (p2 ∨ True)) ∨ ((p4 → p1) ∧ (False ∧ p5))) ∨ (((p0 ∨ p0) → (True → p2)) → False)) ∨ ((((p2 ∨ p4) → False) ∨ ((p0 → False) ∨ (False → False))) ∧ (((True → False) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply True.intro


variable (p4 p0 p7 p1 p5 p3 : Prop)
theorem file17_17256 : ((((((p5 ∨ p4) ∨ (p0 → False)) → ((p7 ∨ p3) ∨ (True ∨ p3))) ∨ (((p7 → False) → (True ∧ p1)) → False)) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p5 ∨ p4) ∨ (p0 → False)) → ((p7 ∨ p3) ∨ (True ∨ p3))) ∨ (((p7 → False) → (True ∧ p1)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inr
        apply Or.inl
        apply True.intro
      case inr assump_9 =>
        apply Or.inr
        apply Or.inl
        apply True.intro
    case inr assump_7 =>
      apply Or.inr
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p4 p0 p7 p6 p2 p3 : Prop)
theorem file17_18027 : (((((True ∨ p1) → False) → ((p6 → p6) ∨ (p4 ∨ False))) → (((p4 → p4) ∨ (p4 → p6)) → False)) → ((((p3 ∧ p2) ∧ (p0 → False)) → ((p6 ∨ p4) ∧ (p6 → p3))) → (((p7 ∧ p3) ∨ (p4 → False)) → ((p3 ∨ p6) → (p4 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_3
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_106 : (((True ∨ p1) → False) → ((p6 → p6) ∨ (p4 ∨ False))) := by
          intro assump_25
          apply Or.inl
          intro assump_28
          exact assump_28
        let assump_24 := assump_1 assump_106
        have assump_107 : ((p4 → p4) ∨ (p4 → p6)) := by
          apply Or.inl
          intro assump_32
          exact assump_32
        let assump_31 := assump_24 assump_107
        apply False.elim assump_31
    case inr assump_13 =>
      have assump_108 : (((True ∨ p1) → False) → ((p6 → p6) ∨ (p4 ∨ False))) := by
        intro assump_45
        apply Or.inl
        intro assump_48
        exact assump_48
      let assump_44 := assump_1 assump_108
      have assump_109 : ((p4 → p4) ∨ (p4 → p6)) := by
        apply Or.inl
        intro assump_52
        exact assump_52
      let assump_51 := assump_44 assump_109
      apply False.elim assump_51
  case inr assump_9 =>
    cases assump_3
    case inl assump_60 =>
      cases assump_60
      case intro assump_62 assump_63 =>
        have assump_110 : (((True ∨ p1) → False) → ((p6 → p6) ∨ (p4 ∨ False))) := by
          intro assump_73
          apply Or.inl
          intro assump_76
          exact assump_76
        let assump_72 := assump_1 assump_110
        have assump_111 : ((p4 → p4) ∨ (p4 → p6)) := by
          apply Or.inl
          intro assump_80
          exact assump_80
        let assump_79 := assump_72 assump_111
        apply False.elim assump_79
    case inr assump_61 =>
      have assump_112 : (((True ∨ p1) → False) → ((p6 → p6) ∨ (p4 ∨ False))) := by
        intro assump_93
        apply Or.inl
        intro assump_96
        exact assump_96
      let assump_92 := assump_1 assump_112
      have assump_113 : ((p4 → p4) ∨ (p4 → p6)) := by
        apply Or.inl
        intro assump_100
        exact assump_100
      let assump_99 := assump_92 assump_113
      apply False.elim assump_99


variable (p0 p3 p1 p2 p4 p5 : Prop)
theorem file17_20445 : (((((True → p0) → (p0 → p3)) → ((p0 ∧ p0) → (False → False))) → False) → ((((False → False) → (p5 ∨ p5)) → ((p0 → False) ∧ (p5 → p2))) → (((False → p3) ∧ (True → p1)) ∨ ((p4 → p4) → False)))) := by
  intro assump_17
  intro assump_18
  apply Or.inl
  apply And.intro
  intro assump_23
  apply False.elim assump_23
  intro assump_26
  have assump_38 : (((True → p0) → (p0 → p3)) → ((p0 ∧ p0) → (False → False))) := by
    intro assump_30
    intro assump_31
    intro assump_32
    apply False.elim assump_32
  let assump_29 := assump_17 assump_38
  apply False.elim assump_29


variable (p3 p2 p6 p4 p0 p5 p7 : Prop)
theorem file17_21084 : (((((False ∧ p4) ∧ (p2 → p6)) ∧ ((p5 ∧ p0) ∧ (p0 → p5))) → False) ∨ ((((p0 → p7) ∨ (p3 → False)) → False) ∨ (((p0 ∧ p0) → (p2 ∧ p5)) ∧ ((p0 → p6) ∧ (p6 → False))))) := by
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p1 p6 p3 p0 p7 p4 p5 : Prop)
theorem file17_21550 : (((((False → True) ∨ (True ∨ p0)) → False) ∨ (((p5 ∧ p4) → False) ∧ ((p4 → False) ∧ (p3 ∧ p4)))) → ((((p7 → False) ∧ (p7 → p0)) → False) ∧ (((p7 ∨ p6) ∨ (p5 ∨ False)) → ((p1 → p1) → (p0 → p6))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      have assump_135 : ((False → True) ∨ (True ∨ p0)) := by
        apply Or.inl
        intro assump_14
        apply True.intro
      let assump_13 := assump_9 assump_135
      apply False.elim assump_13
    case inr assump_10 =>
      cases assump_10
      case intro assump_18 assump_19 =>
        cases assump_19
        case intro assump_22 assump_23 =>
          cases assump_23
          case intro assump_26 assump_27 =>
            have assump_136 : p4 := by
              exact assump_27
            let assump_34 := assump_22 assump_136
            apply False.elim assump_34
  intro assump_38
  intro assump_39
  intro assump_40
  cases assump_38
  case inl assump_45 =>
    cases assump_45
    case inl assump_47 =>
      cases assump_1
      case inl assump_51 =>
        have assump_137 : ((False → True) ∨ (True ∨ p0)) := by
          apply Or.inl
          intro assump_56
          apply True.intro
        let assump_55 := assump_51 assump_137
        apply False.elim assump_55
      case inr assump_52 =>
        cases assump_52
        case intro assump_60 assump_61 =>
          cases assump_61
          case intro assump_64 assump_65 =>
            cases assump_65
            case intro assump_68 assump_69 =>
              have assump_138 : p4 := by
                exact assump_69
              let assump_76 := assump_64 assump_138
              apply False.elim assump_76
    case inr assump_48 =>
      cases assump_1
      case inl assump_82 =>
        exact assump_48
      case inr assump_83 =>
        cases assump_83
        case intro assump_86 assump_87 =>
          cases assump_87
          case intro assump_90 assump_91 =>
            cases assump_91
            case intro assump_94 assump_95 =>
              exact assump_48
  case inr assump_46 =>
    cases assump_46
    case inl assump_100 =>
      cases assump_1
      case inl assump_104 =>
        have assump_139 : ((False → True) ∨ (True ∨ p0)) := by
          apply Or.inl
          intro assump_109
          apply True.intro
        let assump_108 := assump_104 assump_139
        apply False.elim assump_108
      case inr assump_105 =>
        cases assump_105
        case intro assump_113 assump_114 =>
          cases assump_114
          case intro assump_117 assump_118 =>
            cases assump_118
            case intro assump_121 assump_122 =>
              have assump_140 : p4 := by
                exact assump_122
              let assump_129 := assump_117 assump_140
              apply False.elim assump_129
    case inr assump_101 =>
      apply False.elim assump_101


variable (p0 p4 p2 p3 : Prop)
theorem file17_24548 : (((((True → False) → (p3 → False)) → False) ∨ (((p4 ∧ p3) → False) → False)) → ((((False → True) → False) → ((p4 ∨ p0) ∧ (p0 → False))) ∨ (((p4 → False) → (p0 ∨ p2)) ∨ ((p0 → False) ∧ (p3 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply And.intro
    have assump_44 : (False → True) := by
      intro assump_10
      apply True.intro
    let assump_9 := assump_6 assump_44
    apply False.elim assump_9
    intro assump_14
    have assump_45 : (False → True) := by
      intro assump_20
      apply True.intro
    let assump_19 := assump_6 assump_45
    apply False.elim assump_19
  case inr assump_3 =>
    apply Or.inl
    intro assump_26
    apply And.intro
    have assump_46 : (False → True) := by
      intro assump_30
      apply True.intro
    let assump_29 := assump_26 assump_46
    apply False.elim assump_29
    intro assump_34
    have assump_47 : (False → True) := by
      intro assump_40
      apply True.intro
    let assump_39 := assump_26 assump_47
    apply False.elim assump_39


variable (p7 p6 p4 p3 p5 p1 p0 : Prop)
theorem file17_25683 : (((((p4 → p4) → False) → False) ∨ (((p3 → p0) ∧ (p1 ∨ p3)) ∧ ((p7 → False) ∧ (p4 ∨ p0)))) ∧ ((((p3 → p4) ∧ (p0 ∨ p7)) → ((p6 ∨ True) ∧ (p0 → True))) ∧ (((p4 → False) ∧ (p5 → False)) → ((False → False) ∨ (p7 ∧ p3))))) := by
  apply And.intro
  apply Or.inl
  intro assump_79
  have assump_111 : (p4 → p4) := by
    intro assump_83
    exact assump_83
  let assump_82 := assump_79 assump_111
  apply False.elim assump_82
  apply And.intro
  intro assump_89
  apply And.intro
  cases assump_89
  case intro assump_90 assump_91 =>
    cases assump_91
    case inl assump_94 =>
      apply Or.inr
      apply True.intro
    case inr assump_95 =>
      apply Or.inr
      apply True.intro
  intro assump_100
  apply True.intro
  intro assump_101
  cases assump_101
  case intro assump_102 assump_103 =>
    apply Or.inl
    intro assump_108
    apply False.elim assump_108


variable (p3 p4 p1 p0 p7 : Prop)
theorem file17_26607 : ((((((p7 ∧ p0) ∧ (p7 → p1)) → False) → (((True ∨ p3) ∨ (p7 → p7)) ∨ ((p4 ∧ p3) ∧ (True → False)))) → False) → False) := by
  intro assump_17
  have assump_27 : ((((p7 ∧ p0) ∧ (p7 → p1)) → False) → (((True ∨ p3) ∨ (p7 → p7)) ∨ ((p4 ∧ p3) ∧ (True → False)))) := by
    intro assump_21
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_20 := assump_17 assump_27
  apply False.elim assump_20


variable (p1 p0 p7 p4 p3 p5 p6 : Prop)
theorem file17_27093 : (((((False → False) ∨ (p7 → False)) ∨ ((p5 ∨ p3) → False)) ∨ (((p3 → p6) → (p3 ∨ p0)) ∧ ((p7 ∧ p3) → (p3 → False)))) ∨ ((((p5 ∧ p1) ∧ (p3 → p4)) → ((p7 ∨ False) ∨ (p1 ∧ True))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p4 p0 p2 p7 p5 p6 : Prop)
theorem file17_27451 : ((((((p5 ∨ p2) ∨ (p2 → False)) → ((True → True) → False)) → (((p0 → False) → (p2 → p6)) ∧ ((p2 ∧ p7) → (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_41 : ((((p5 ∨ p2) ∨ (p2 → False)) → ((True → True) → False)) → (((p0 → False) → (p2 → p6)) ∧ ((p2 ∧ p7) → (p4 → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    have assump_42 : ((p5 ∨ p2) ∨ (p2 → False)) := by
      apply Or.inl
      apply Or.inr
      exact assump_7
    let assump_14 := assump_5 assump_42
    have assump_43 : (True → True) := by
      intro assump_16
      apply True.intro
    let assump_15 := assump_14 assump_43
    apply False.elim assump_15
    intro assump_20
    intro assump_21
    cases assump_20
    case intro assump_24 assump_25 =>
      have assump_44 : ((p5 ∨ p2) ∨ (p2 → False)) := by
        apply Or.inl
        apply Or.inr
        exact assump_24
      let assump_32 := assump_5 assump_44
      have assump_45 : (True → True) := by
        intro assump_34
        apply True.intro
      let assump_33 := assump_32 assump_45
      apply False.elim assump_33
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p2 p6 p3 p5 p4 p7 : Prop)
theorem file17_28696 : ((((((False ∧ p3) ∨ (p4 ∧ False)) ∨ ((p7 ∨ p5) ∨ (p7 → p5))) → (((True → False) → (p4 ∧ p6)) → False)) ∧ ((((p7 ∧ p2) → False) → False) ∧ (((p5 → False) ∧ (p2 → False)) ∨ ((p2 → False) ∧ (False → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_63 : ((p7 ∧ p2) → False) := by
            intro assump_21
            cases assump_21
            case intro assump_22 assump_23 =>
              have assump_64 : p2 := by
                exact assump_23
              let assump_30 := assump_13 assump_64
              apply False.elim assump_30
          let assump_20 := assump_6 assump_63
          apply False.elim assump_20
      case inr assump_11 =>
        cases assump_11
        case intro assump_37 assump_38 =>
          have assump_65 : ((p7 ∧ p2) → False) := by
            intro assump_46
            cases assump_46
            case intro assump_47 assump_48 =>
              have assump_66 : p2 := by
                exact assump_48
              let assump_56 := assump_37 assump_66
              apply False.elim assump_56
          let assump_45 := assump_6 assump_65
          apply False.elim assump_45


variable (p5 p0 p3 p4 p1 p6 : Prop)
theorem file17_30114 : ((((((p3 → False) → False) → ((p0 ∧ p6) → False)) → (((p6 → False) ∧ (p4 → p1)) → ((p3 → p1) → (p5 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p3 → False) → False) → ((p0 ∧ p6) → False)) → (((p6 → False) ∧ (p4 → p1)) → ((p3 → p1) → (p5 ∨ True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p1 p4 p0 p2 p3 p6 : Prop)
theorem file17_30679 : ((((((p0 ∨ p6) ∧ (p1 ∨ p2)) ∧ ((p0 ∧ p4) → False)) → (((p3 → p0) → (p1 → False)) ∨ ((p2 ∨ False) ∨ (p6 ∨ p0)))) ∧ ((((p0 → p4) → (p0 → True)) ∧ ((False ∧ p2) ∨ (True ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_14 : (((p0 → p4) → (p0 → True)) ∧ ((False ∧ p2) ∨ (True ∨ p3))) := by
      apply And.intro
      intro assump_9
      intro assump_10
      apply True.intro
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_14
    apply False.elim assump_8


variable (p2 p7 p3 p0 p1 p4 p5 : Prop)
theorem file17_31313 : (((((True ∧ True) ∧ (False ∧ True)) → False) ∨ (((p5 ∨ p4) → (p0 ∧ p2)) ∨ ((p1 ∧ p2) ∨ (p7 → True)))) ∨ ((((p5 ∧ p2) → False) ∨ ((p3 ∨ p2) ∧ (True → p4))) ∨ (((p3 → False) ∨ (True ∨ p0)) ∨ ((p1 ∧ p7) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply False.elim assump_10


variable (p6 p2 p3 p5 p7 p1 : Prop)
theorem file17_31840 : (((((False → False) → (p2 ∨ p1)) ∨ ((p5 ∨ p6) → False)) → False) → ((((p6 → True) ∨ (p7 ∧ p2)) → False) → (((False → False) → (p7 ∧ p3)) → ((p2 ∨ p2) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_37 : (((False → False) → (p2 ∨ p1)) ∨ ((p5 ∨ p6) → False)) := by
      apply Or.inl
      intro assump_16
      apply Or.inl
      exact assump_5
    let assump_15 := assump_1 assump_37
    apply False.elim assump_15
  case inr assump_6 =>
    have assump_38 : (((False → False) → (p2 ∨ p1)) ∨ ((p5 ∨ p6) → False)) := by
      apply Or.inl
      intro assump_31
      apply Or.inl
      exact assump_6
    let assump_30 := assump_1 assump_38
    apply False.elim assump_30


variable (p5 p7 p2 p1 p4 p3 p0 : Prop)
theorem file17_32668 : (((((p3 ∨ p4) ∨ (p1 → False)) ∨ ((True ∨ p4) → False)) ∨ (((p5 → False) → False) ∨ ((p4 → p7) ∧ (False → p4)))) → ((((p1 ∧ p7) ∨ (False → True)) ∨ ((p4 → p4) → False)) ∨ (((p2 → p1) → False) ∧ ((p0 → True) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          intro assump_12
          apply True.intro
        case inr assump_9 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          intro assump_15
          apply True.intro
      case inr assump_7 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        intro assump_18
        apply True.intro
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      intro assump_21
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_22 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      intro assump_26
      apply True.intro
    case inr assump_23 =>
      cases assump_23
      case intro assump_27 assump_28 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        intro assump_33
        apply True.intro


variable (p4 p6 p2 p5 p0 p1 : Prop)
theorem file17_34062 : (((((p6 ∧ p1) → (p6 → False)) → ((p2 ∨ True) → (p6 → False))) → False) → ((((p0 ∨ p4) → (True ∨ True)) ∨ ((p2 ∧ p6) ∧ (p5 → False))) ∨ (((p4 ∨ p1) ∧ (False → p0)) → ((p0 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply Or.inl
    apply True.intro
  case inr assump_6 =>
    apply Or.inl
    apply True.intro


variable (p6 p5 p7 p0 : Prop)
theorem file17_34516 : ((((((True ∧ p6) ∧ (p5 ∧ False)) ∧ ((p0 ∧ p7) → (False → p7))) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True ∧ p6) ∧ (p5 ∧ False)) ∧ ((p0 ∧ p7) → (False → p7))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p1 p3 p2 p5 p6 : Prop)
theorem file17_35155 : (((((p5 → False) → False) → False) → (((p5 → False) ∨ (False ∧ True)) ∨ ((False → p0) → (p1 → False)))) ∨ ((((p0 → False) ∨ (True → p2)) ∨ ((p6 ∨ p6) → (True → False))) ∧ (((p2 → False) ∨ (p3 → False)) ∨ ((p0 → False) ∨ (p5 → p2))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_19 : ((p5 → False) → False) := by
    intro assump_9
    have assump_20 : p5 := by
      exact assump_4
    let assump_12 := assump_9 assump_20
    apply False.elim assump_12
  let assump_8 := assump_1 assump_19
  apply False.elim assump_8


variable (p1 p6 p0 p7 p4 p5 : Prop)
theorem file17_35788 : ((((((p5 ∨ True) ∨ (p6 → False)) → ((p5 ∧ p5) → False)) ∧ (((p7 ∨ False) ∨ (p4 ∧ p4)) → False)) ∧ ((((p0 ∨ p1) → (False ∨ p6)) → ((False ∧ p5) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_22 : (((p0 ∨ p1) → (False ∨ p6)) → ((False ∧ p5) → False)) := by
        intro assump_13
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
      let assump_12 := assump_3 assump_22
      apply False.elim assump_12


variable (p6 p4 p1 p7 p0 p2 p5 : Prop)
theorem file17_36461 : (((((p6 → False) → (p7 → False)) ∨ ((p2 → False) → False)) ∧ (((p7 ∨ p6) ∨ (p1 → p1)) → False)) → ((((p1 ∧ p0) ∧ (p5 ∧ p7)) → False) → (((p5 → p2) → (p4 → False)) ∨ ((False → False) → (False ∨ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      intro assump_13
      intro assump_14
      have assump_47 : ((p7 ∨ p6) ∨ (p1 → p1)) := by
        apply Or.inr
        intro assump_22
        exact assump_22
      let assump_21 := assump_6 assump_47
      apply False.elim assump_21
    case inr assump_8 =>
      apply Or.inl
      intro assump_32
      intro assump_33
      have assump_48 : ((p7 ∨ p6) ∨ (p1 → p1)) := by
        apply Or.inr
        intro assump_41
        exact assump_41
      let assump_40 := assump_6 assump_48
      apply False.elim assump_40


variable (p0 p4 p1 p5 p2 p7 p3 : Prop)
theorem file17_37408 : ((((((True → p0) → (p2 → False)) ∧ ((p5 ∧ False) → (p0 ∧ p5))) → (((p7 ∨ p5) → (p2 → p4)) ∨ ((p0 ∧ p4) ∨ (p2 ∨ p3)))) ∧ ((((True ∨ p5) → (p4 ∧ p1)) → ((False ∨ False) → (p5 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((True ∨ p5) → (p4 ∧ p1)) → ((False ∨ False) → (p5 → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_10
      case inl assump_14 =>
        apply False.elim assump_14
      case inr assump_15 =>
        apply False.elim assump_15
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p7 p0 p5 p4 p1 p3 : Prop)
theorem file17_38117 : (((((False ∧ p7) ∨ (p0 → p1)) ∧ ((p5 ∨ p3) → (p5 → False))) ∧ (((p4 ∧ False) → (False → p3)) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      case inr assump_11 =>
        have assump_30 : ((p4 ∧ False) → (False → p3)) := by
          intro assump_23
          intro assump_24
          apply False.elim assump_24
        let assump_22 := assump_7 assump_30
        apply False.elim assump_22


variable (p4 p2 p3 p0 p1 : Prop)
theorem file17_38824 : ((((((p4 ∧ p3) ∧ (p2 → False)) → False) ∧ (((p2 ∨ p4) → False) ∨ ((p1 ∨ p0) ∨ (True ∧ p2)))) ∧ ((((p2 ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_78 : (((p2 ∨ True) → False) → False) := by
          intro assump_15
          have assump_79 : (p2 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_18 := assump_15 assump_79
          apply False.elim assump_18
        let assump_14 := assump_3 assump_78
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case inl assump_25 =>
          cases assump_25
          case inl assump_27 =>
            have assump_80 : (((p2 ∨ True) → False) → False) := by
              intro assump_34
              have assump_81 : (p2 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_37 := assump_34 assump_81
              apply False.elim assump_37
            let assump_33 := assump_3 assump_80
            apply False.elim assump_33
          case inr assump_28 =>
            have assump_82 : (((p2 ∨ True) → False) → False) := by
              intro assump_49
              have assump_83 : (p2 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_52 := assump_49 assump_83
              apply False.elim assump_52
            let assump_48 := assump_3 assump_82
            apply False.elim assump_48
        case inr assump_26 =>
          cases assump_26
          case intro assump_59 assump_60 =>
            have assump_84 : (((p2 ∨ True) → False) → False) := by
              intro assump_68
              have assump_85 : (p2 ∨ True) := by
                apply Or.inl
                exact assump_60
              let assump_71 := assump_68 assump_85
              apply False.elim assump_71
            let assump_67 := assump_3 assump_84
            apply False.elim assump_67


variable (p5 p6 p4 p0 p2 : Prop)
theorem file17_40986 : (((((False ∧ p6) → (p2 → p5)) → ((p2 → False) → False)) → False) → ((((p2 → p0) ∧ (True → False)) → False) → (((p6 → p0) → (p4 → False)) → ((p5 → False) → (False → False))))) := by
  intro assump_19
  intro assump_20
  intro assump_21
  intro assump_22
  intro assump_23
  apply False.elim assump_23


variable (p2 p4 p6 p1 p0 p7 : Prop)
theorem file17_41346 : (((((p2 ∨ p6) ∧ (p1 → p1)) ∨ ((p2 ∨ p7) → False)) → False) → ((((p7 → False) ∧ (p4 ∨ p6)) → False) ∨ (((False ∧ p4) ∨ (p0 → False)) ∨ ((True → False) ∨ (True → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      have assump_53 : (((p2 ∨ p6) ∧ (p1 → p1)) ∨ ((p2 ∨ p7) → False)) := by
        apply Or.inr
        intro assump_16
        cases assump_16
        case inl assump_17 =>
          have assump_54 : (((p2 ∨ p6) ∧ (p1 → p1)) ∨ ((p2 ∨ p7) → False)) := by
            apply Or.inl
            apply And.intro
            apply Or.inl
            exact assump_17
            intro assump_25
            exact assump_25
          let assump_24 := assump_1 assump_54
          apply False.elim assump_24
        case inr assump_18 =>
          have assump_55 : p7 := by
            exact assump_18
          let assump_35 := assump_5 assump_55
          apply False.elim assump_35
      let assump_15 := assump_1 assump_53
      apply False.elim assump_15
    case inr assump_10 =>
      have assump_56 : (((p2 ∨ p6) ∧ (p1 → p1)) ∨ ((p2 ∨ p7) → False)) := by
        apply Or.inl
        apply And.intro
        apply Or.inr
        exact assump_10
        intro assump_47
        exact assump_47
      let assump_46 := assump_1 assump_56
      apply False.elim assump_46


variable (p3 p2 p1 p7 p6 p0 p5 p4 : Prop)
theorem file17_42803 : (((((p2 ∨ p1) ∧ (False → False)) → False) ∧ (((p3 ∨ False) ∧ (p4 ∨ True)) ∧ ((p5 → p5) ∧ (p4 ∨ p0)))) → ((((False → False) ∧ (True ∨ True)) → False) → (((p6 ∧ True) ∨ (p3 → False)) ∧ ((p0 → p4) → (p7 → p5))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case inl assump_17 =>
            cases assump_10
            case intro assump_21 assump_22 =>
              cases assump_22
              case inl assump_25 =>
                apply Or.inr
                intro assump_29
                have assump_201 : ((False → False) ∧ (True ∨ True)) := by
                  apply And.intro
                  intro assump_39
                  apply False.elim assump_39
                  apply Or.inl
                  apply True.intro
                let assump_38 := assump_2 assump_201
                apply False.elim assump_38
              case inr assump_26 =>
                apply Or.inr
                intro assump_47
                have assump_202 : ((False → False) ∧ (True ∨ True)) := by
                  apply And.intro
                  intro assump_57
                  apply False.elim assump_57
                  apply Or.inl
                  apply True.intro
                let assump_56 := assump_2 assump_202
                apply False.elim assump_56
          case inr assump_18 =>
            cases assump_10
            case intro assump_65 assump_66 =>
              cases assump_66
              case inl assump_69 =>
                apply Or.inr
                intro assump_73
                have assump_203 : ((False → False) ∧ (True ∨ True)) := by
                  apply And.intro
                  intro assump_82
                  apply False.elim assump_82
                  apply Or.inl
                  apply True.intro
                let assump_81 := assump_2 assump_203
                apply False.elim assump_81
              case inr assump_70 =>
                apply Or.inr
                intro assump_90
                have assump_204 : ((False → False) ∧ (True ∨ True)) := by
                  apply And.intro
                  intro assump_99
                  apply False.elim assump_99
                  apply Or.inl
                  apply True.intro
                let assump_98 := assump_2 assump_204
                apply False.elim assump_98
        case inr assump_14 =>
          apply False.elim assump_14
  intro assump_107
  intro assump_108
  cases assump_1
  case intro assump_115 assump_116 =>
    cases assump_116
    case intro assump_119 assump_120 =>
      cases assump_119
      case intro assump_121 assump_122 =>
        cases assump_121
        case inl assump_123 =>
          cases assump_122
          case inl assump_127 =>
            cases assump_120
            case intro assump_131 assump_132 =>
              cases assump_132
              case inl assump_135 =>
                have assump_205 : ((False → False) ∧ (True ∨ True)) := by
                  apply And.intro
                  intro assump_145
                  apply False.elim assump_145
                  apply Or.inl
                  apply True.intro
                let assump_144 := assump_2 assump_205
                apply False.elim assump_144
              case inr assump_136 =>
                have assump_206 : ((False → False) ∧ (True ∨ True)) := by
                  apply And.intro
                  intro assump_159
                  apply False.elim assump_159
                  apply Or.inl
                  apply True.intro
                let assump_158 := assump_2 assump_206
                apply False.elim assump_158
          case inr assump_128 =>
            cases assump_120
            case intro assump_167 assump_168 =>
              cases assump_168
              case inl assump_171 =>
                have assump_207 : ((False → False) ∧ (True ∨ True)) := by
                  apply And.intro
                  intro assump_180
                  apply False.elim assump_180
                  apply Or.inl
                  apply True.intro
                let assump_179 := assump_2 assump_207
                apply False.elim assump_179
              case inr assump_172 =>
                have assump_208 : ((False → False) ∧ (True ∨ True)) := by
                  apply And.intro
                  intro assump_193
                  apply False.elim assump_193
                  apply Or.inl
                  apply True.intro
                let assump_192 := assump_2 assump_208
                apply False.elim assump_192
        case inr assump_124 =>
          apply False.elim assump_124


variable (p2 p7 p4 p1 : Prop)
theorem file17_47709 : ((((((p1 ∨ True) → (p7 ∧ p7)) → ((p2 → p2) ∨ (p4 → p1))) ∨ (((p1 → p2) ∨ (False → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p1 ∨ True) → (p7 ∧ p7)) → ((p2 → p2) ∨ (p4 → p1))) ∨ (((p1 → p2) ∨ (False → False)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p5 p0 p1 p4 p6 : Prop)
theorem file17_48189 : ((((((p6 ∧ False) ∧ (p6 ∨ p1)) → False) ∨ (((p4 ∨ False) ∧ (p7 → p0)) → False)) → ((((False ∧ False) ∨ (False → False)) ∨ ((p5 → False) ∧ (p7 → p7))) → False)) → False) := by
  intro assump_5
  have assump_25 : ((((p6 ∧ False) ∧ (p6 ∨ p1)) → False) ∨ (((p4 ∨ False) ∧ (p7 → p0)) → False)) := by
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
  let assump_8 := assump_5 assump_25
  have assump_26 : (((False ∧ False) ∨ (False → False)) ∨ ((p5 → False) ∧ (p7 → p7))) := by
    apply Or.inl
    apply Or.inr
    intro assump_19
    apply False.elim assump_19
  let assump_18 := assump_8 assump_26
  apply False.elim assump_18


variable (p7 p3 p6 p4 p1 p2 : Prop)
theorem file17_49015 : ((((((p2 → False) ∨ (p6 → p7)) → ((True ∧ False) ∨ (p1 ∨ p6))) → (((p3 ∨ p4) ∧ (False ∨ p7)) → ((p3 → False) → (p7 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p2 → False) ∨ (p6 → p7)) → ((True ∧ False) ∨ (p1 ∨ p6))) → (((p3 ∨ p4) ∧ (False ∨ p7)) → ((p3 → False) → (p7 ∧ True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case inl assump_16 =>
          apply False.elim assump_16
        case inr assump_17 =>
          exact assump_17
      case inr assump_13 =>
        cases assump_11
        case inl assump_26 =>
          apply False.elim assump_26
        case inr assump_27 =>
          exact assump_27
    apply True.intro
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p3 p6 p2 p7 p4 : Prop)
theorem file17_49980 : (((((p3 ∧ p4) ∨ (p6 ∧ False)) ∨ ((p2 ∧ p3) → (p7 ∨ p3))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p3 ∧ p4) ∨ (p6 ∧ False)) ∨ ((p2 ∧ p3) → (p7 ∨ p3))) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      exact assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p7 : Prop)
theorem file17_50402 : ((((((p7 → p3) ∨ (p3 ∧ p7)) ∧ ((p3 ∧ False) ∨ (True → False))) → False) → False) → False) := by
  intro assump_1
  have assump_49 : ((((p7 → p3) ∨ (p3 ∧ p7)) ∧ ((p3 ∧ False) ∨ (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
        case inr assump_13 =>
          have assump_50 : True := by
            apply True.intro
          let assump_22 := assump_13 assump_50
          apply False.elim assump_22
      case inr assump_9 =>
        cases assump_9
        case intro assump_26 assump_27 =>
          cases assump_7
          case inl assump_32 =>
            cases assump_32
            case intro assump_34 assump_35 =>
              apply False.elim assump_35
          case inr assump_33 =>
            have assump_51 : True := by
              apply True.intro
            let assump_42 := assump_33 assump_51
            apply False.elim assump_42
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p6 p0 p5 p4 p2 p1 : Prop)
theorem file17_51655 : (((((True ∨ p1) ∨ (p6 → p2)) → False) → (((p0 → p6) ∧ (p4 → False)) ∨ ((p2 → p2) → False))) ∧ ((((False ∧ p5) → (p0 ∨ p1)) → False) → False)) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_32 : ((True ∨ p1) ∨ (p6 → p2)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_8 := assump_1 assump_32
  apply False.elim assump_8
  intro assump_12
  have assump_33 : ((True ∨ p1) ∨ (p6 → p2)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_16 := assump_1 assump_33
  apply False.elim assump_16
  intro assump_20
  have assump_34 : ((False ∧ p5) → (p0 ∨ p1)) := by
    intro assump_24
    cases assump_24
    case intro assump_25 assump_26 =>
      apply False.elim assump_25
  let assump_23 := assump_20 assump_34
  apply False.elim assump_23


variable (p2 p0 p7 p3 p4 p5 p6 p1 : Prop)
theorem file17_52565 : (((((p1 ∧ p3) ∨ (p6 → p1)) → False) ∨ (((False ∨ False) → False) ∧ ((p3 ∧ p5) → (p0 → p3)))) → ((((False → False) → False) ∧ ((p7 → False) ∨ (p2 ∨ p6))) → (((p2 → False) → (p1 → p5)) ∧ ((False → p6) ∨ (p4 ∨ False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_10
    case inl assump_13 =>
      cases assump_1
      case inl assump_17 =>
        have assump_166 : ((p1 ∧ p3) ∨ (p6 → p1)) := by
          apply Or.inr
          intro assump_22
          exact assump_4
        let assump_21 := assump_17 assump_166
        apply False.elim assump_21
      case inr assump_18 =>
        cases assump_18
        case intro assump_28 assump_29 =>
          have assump_167 : (False → False) := by
            intro assump_38
            apply False.elim assump_38
          let assump_37 := assump_9 assump_167
          apply False.elim assump_37
    case inr assump_14 =>
      cases assump_14
      case inl assump_44 =>
        cases assump_1
        case inl assump_48 =>
          have assump_168 : ((p1 ∧ p3) ∨ (p6 → p1)) := by
            apply Or.inr
            intro assump_53
            exact assump_4
          let assump_52 := assump_48 assump_168
          apply False.elim assump_52
        case inr assump_49 =>
          cases assump_49
          case intro assump_59 assump_60 =>
            have assump_169 : (False → False) := by
              intro assump_69
              apply False.elim assump_69
            let assump_68 := assump_9 assump_169
            apply False.elim assump_68
      case inr assump_45 =>
        cases assump_1
        case inl assump_77 =>
          have assump_170 : ((p1 ∧ p3) ∨ (p6 → p1)) := by
            apply Or.inr
            intro assump_82
            exact assump_4
          let assump_81 := assump_77 assump_170
          apply False.elim assump_81
        case inr assump_78 =>
          cases assump_78
          case intro assump_88 assump_89 =>
            have assump_171 : (False → False) := by
              intro assump_98
              apply False.elim assump_98
            let assump_97 := assump_9 assump_171
            apply False.elim assump_97
  cases assump_2
  case intro assump_104 assump_105 =>
    cases assump_105
    case inl assump_108 =>
      cases assump_1
      case inl assump_112 =>
        apply Or.inl
        intro assump_116
        apply False.elim assump_116
      case inr assump_113 =>
        cases assump_113
        case intro assump_119 assump_120 =>
          apply Or.inl
          intro assump_125
          apply False.elim assump_125
    case inr assump_109 =>
      cases assump_109
      case inl assump_128 =>
        cases assump_1
        case inl assump_132 =>
          apply Or.inl
          intro assump_136
          apply False.elim assump_136
        case inr assump_133 =>
          cases assump_133
          case intro assump_139 assump_140 =>
            apply Or.inl
            intro assump_145
            apply False.elim assump_145
      case inr assump_129 =>
        cases assump_1
        case inl assump_150 =>
          apply Or.inl
          intro assump_154
          apply False.elim assump_154
        case inr assump_151 =>
          cases assump_151
          case intro assump_157 assump_158 =>
            apply Or.inl
            intro assump_163
            apply False.elim assump_163


variable (p0 p6 p7 p2 p1 p4 p3 : Prop)
theorem file17_56078 : (((((p6 → True) → (False ∨ True)) ∨ ((p7 ∨ p0) ∧ (p2 ∨ False))) ∨ (((p0 → False) ∨ (False ∨ p0)) ∨ ((True ∨ p4) → False))) ∨ ((((p1 ∧ p6) ∨ (p4 → False)) ∨ ((p7 → p3) → (p1 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply True.intro


variable (p2 p3 p0 p4 p5 p7 p6 p1 : Prop)
theorem file17_56440 : (((((p4 → p6) ∧ (p7 ∧ p3)) → ((p0 ∨ p0) → (p1 → False))) → (((p5 → p0) ∨ (p4 → p2)) → False)) → ((((p2 ∨ p6) ∧ (p4 → False)) → ((False → p3) ∨ (p1 ∨ p5))) ∨ (((True ∨ p1) ∨ (p1 → False)) ∧ ((p5 → False) ∨ (True → p0))))) := by
  intro assump_25
  apply Or.inl
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    cases assump_29
    case inl assump_31 =>
      apply Or.inl
      intro assump_37
      apply False.elim assump_37
    case inr assump_32 =>
      apply Or.inl
      intro assump_44
      apply False.elim assump_44


variable (p4 p2 p5 p1 p0 p7 p6 : Prop)
theorem file17_57055 : (((((p5 ∧ False) ∧ (p1 ∧ p6)) ∧ ((p2 → p6) ∧ (False → p4))) ∧ (((p5 → False) → (True ∨ p1)) ∧ ((False ∨ False) → False))) ∨ ((((p1 → False) ∨ (p7 → p1)) → False) → (((p5 ∨ True) ∨ (p0 → False)) → ((False → p5) ∨ (p6 → p6))))) := by
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      intro assump_11
      apply False.elim assump_11
    case inr assump_6 =>
      apply Or.inl
      intro assump_18
      apply False.elim assump_18
  case inr assump_4 =>
    apply Or.inl
    intro assump_25
    apply False.elim assump_25


variable (p4 p3 p1 p7 : Prop)
theorem file17_57738 : ((((((p7 → False) → False) ∨ ((True → False) ∨ (p1 ∨ p4))) → False) ∧ ((((True ∨ p1) ∧ (p3 ∧ False)) → ((p1 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_36 : (((True ∨ p1) ∧ (p3 ∧ False)) → ((p1 → False) → False)) := by
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
          cases assump_14
          case intro assump_27 assump_28 =>
            apply False.elim assump_28
    let assump_8 := assump_3 assump_36
    apply False.elim assump_8


variable (p7 p2 p1 : Prop)
theorem file17_58567 : ((((((p2 ∧ True) ∧ (p7 ∧ False)) ∧ ((p1 → p7) ∨ (False ∨ False))) → False) → False) → False) := by
  intro assump_5
  have assump_29 : ((((p2 ∧ True) ∧ (p7 ∧ False)) ∧ ((p1 → p7) ∨ (False ∨ False))) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_13
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
  let assump_8 := assump_5 assump_29
  apply False.elim assump_8


variable (p2 p6 p1 p5 p4 p0 p3 : Prop)
theorem file17_59222 : ((((((p5 ∧ p6) → (False ∨ p6)) ∨ ((p3 ∧ p4) ∧ (p6 ∨ p6))) → (((p1 → False) → False) ∧ ((p6 ∧ p5) ∨ (p4 ∧ p1)))) ∧ ((((p5 ∨ p5) ∨ (p0 ∨ p5)) ∧ ((p5 ∧ p2) ∧ (p6 ∧ False))) ∧ (((True ∨ p2) → False) → ((p1 → p6) ∧ (p0 → False))))) → False) := by
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
          case inl assump_12 =>
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_17
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
          case inr assump_13 =>
            cases assump_9
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                cases assump_33
                case intro assump_40 assump_41 =>
                  apply False.elim assump_41
        case inr assump_11 =>
          cases assump_11
          case inl assump_46 =>
            cases assump_9
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_51
                case intro assump_58 assump_59 =>
                  apply False.elim assump_59
          case inr assump_47 =>
            cases assump_9
            case intro assump_66 assump_67 =>
              cases assump_66
              case intro assump_68 assump_69 =>
                cases assump_67
                case intro assump_74 assump_75 =>
                  apply False.elim assump_75


variable (p7 p5 p3 p1 p6 : Prop)
theorem file17_61078 : (((((p6 → p6) → False) ∧ ((p5 ∨ False) → False)) ∧ (((p1 ∨ False) ∧ (p7 ∧ p7)) → False)) → ((((False → False) → (p7 ∧ p3)) → False) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      have assump_28 : (p6 → p6) := by
        intro assump_22
        exact assump_22
      let assump_21 := assump_11 assump_28
      apply False.elim assump_21


variable (p7 p3 p2 p0 p4 p6 p1 : Prop)
theorem file17_61595 : ((((((p0 → False) → (p6 ∨ False)) ∨ ((False ∧ True) → False)) → False) ∧ ((((p0 ∨ True) → (False ∧ p1)) → ((p2 ∧ p7) ∧ (False → p3))) → (((p4 ∧ True) ∨ (p4 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_58 : (((p0 ∨ True) → (False ∧ p1)) → ((p2 ∧ p7) ∧ (False → p3))) := by
      intro assump_9
      apply And.intro
      apply And.intro
      have assump_59 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_9 assump_59
      let assump_13 := And.left assump_12
      apply False.elim assump_13
      have assump_60 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_19 := assump_9 assump_60
      let assump_20 := And.left assump_19
      apply False.elim assump_20
      intro assump_24
      apply False.elim assump_24
    let assump_8 := assump_3 assump_58
    have assump_61 : ((p4 ∧ True) ∨ (p4 → False)) := by
      apply Or.inr
      intro assump_28
      have assump_62 : (((p0 ∨ True) → (False ∧ p1)) → ((p2 ∧ p7) ∧ (False → p3))) := by
        intro assump_33
        apply And.intro
        apply And.intro
        have assump_63 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_36 := assump_33 assump_63
        let assump_37 := And.left assump_36
        apply False.elim assump_37
        have assump_64 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_43 := assump_33 assump_64
        let assump_44 := And.left assump_43
        apply False.elim assump_44
        intro assump_48
        apply False.elim assump_48
      let assump_32 := assump_3 assump_62
      have assump_65 : ((p4 ∧ True) ∨ (p4 → False)) := by
        apply Or.inl
        apply And.intro
        exact assump_28
        apply True.intro
      let assump_51 := assump_32 assump_65
      apply False.elim assump_51
    let assump_27 := assump_8 assump_61
    apply False.elim assump_27


variable (p1 p3 p0 : Prop)
theorem file17_63652 : (((((p0 ∧ False) ∨ (False → True)) → False) → False) ∨ ((((p1 → False) ∧ (p3 → False)) → False) → (((p0 ∨ True) ∨ (False ∨ False)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p0 ∧ False) ∨ (False → True)) := by
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p3 p6 p4 p5 p2 p7 : Prop)
theorem file17_64069 : (((((p5 → p7) ∨ (p7 ∧ p4)) ∨ ((p6 ∧ p5) → (p4 → p7))) ∧ (((p5 → True) → False) ∧ ((True → p7) ∨ (False → False)))) → ((((False → False) ∨ (True → False)) ∨ ((p3 → p2) ∧ (False ∨ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_11
          case inl assump_13 =>
            cases assump_10
            case intro assump_17 assump_18 =>
              cases assump_18
              case inl assump_21 =>
                have assump_276 : (p5 → True) := by
                  intro assump_28
                  apply True.intro
                let assump_27 := assump_17 assump_276
                apply False.elim assump_27
              case inr assump_22 =>
                have assump_277 : (p5 → True) := by
                  intro assump_36
                  apply True.intro
                let assump_35 := assump_17 assump_277
                apply False.elim assump_35
          case inr assump_14 =>
            cases assump_14
            case intro assump_40 assump_41 =>
              cases assump_10
              case intro assump_46 assump_47 =>
                cases assump_47
                case inl assump_50 =>
                  have assump_278 : (p5 → True) := by
                    intro assump_57
                    apply True.intro
                  let assump_56 := assump_46 assump_278
                  apply False.elim assump_56
                case inr assump_51 =>
                  have assump_279 : (p5 → True) := by
                    intro assump_65
                    apply True.intro
                  let assump_64 := assump_46 assump_279
                  apply False.elim assump_64
        case inr assump_12 =>
          cases assump_10
          case intro assump_71 assump_72 =>
            cases assump_72
            case inl assump_75 =>
              have assump_280 : (p5 → True) := by
                intro assump_82
                apply True.intro
              let assump_81 := assump_71 assump_280
              apply False.elim assump_81
            case inr assump_76 =>
              have assump_281 : (p5 → True) := by
                intro assump_90
                apply True.intro
              let assump_89 := assump_71 assump_281
              apply False.elim assump_89
    case inr assump_6 =>
      cases assump_1
      case intro assump_96 assump_97 =>
        cases assump_96
        case inl assump_98 =>
          cases assump_98
          case inl assump_100 =>
            cases assump_97
            case intro assump_104 assump_105 =>
              cases assump_105
              case inl assump_108 =>
                have assump_282 : (p5 → True) := by
                  intro assump_115
                  apply True.intro
                let assump_114 := assump_104 assump_282
                apply False.elim assump_114
              case inr assump_109 =>
                have assump_283 : (p5 → True) := by
                  intro assump_123
                  apply True.intro
                let assump_122 := assump_104 assump_283
                apply False.elim assump_122
          case inr assump_101 =>
            cases assump_101
            case intro assump_127 assump_128 =>
              cases assump_97
              case intro assump_133 assump_134 =>
                cases assump_134
                case inl assump_137 =>
                  have assump_284 : (p5 → True) := by
                    intro assump_144
                    apply True.intro
                  let assump_143 := assump_133 assump_284
                  apply False.elim assump_143
                case inr assump_138 =>
                  have assump_285 : (p5 → True) := by
                    intro assump_152
                    apply True.intro
                  let assump_151 := assump_133 assump_285
                  apply False.elim assump_151
        case inr assump_99 =>
          cases assump_97
          case intro assump_158 assump_159 =>
            cases assump_159
            case inl assump_162 =>
              have assump_286 : (p5 → True) := by
                intro assump_169
                apply True.intro
              let assump_168 := assump_158 assump_286
              apply False.elim assump_168
            case inr assump_163 =>
              have assump_287 : (p5 → True) := by
                intro assump_177
                apply True.intro
              let assump_176 := assump_158 assump_287
              apply False.elim assump_176
  case inr assump_4 =>
    cases assump_4
    case intro assump_181 assump_182 =>
      cases assump_182
      case inl assump_185 =>
        apply False.elim assump_185
      case inr assump_186 =>
        cases assump_1
        case intro assump_191 assump_192 =>
          cases assump_191
          case inl assump_193 =>
            cases assump_193
            case inl assump_195 =>
              cases assump_192
              case intro assump_199 assump_200 =>
                cases assump_200
                case inl assump_203 =>
                  have assump_288 : (p5 → True) := by
                    intro assump_210
                    apply True.intro
                  let assump_209 := assump_199 assump_288
                  apply False.elim assump_209
                case inr assump_204 =>
                  have assump_289 : (p5 → True) := by
                    intro assump_218
                    apply True.intro
                  let assump_217 := assump_199 assump_289
                  apply False.elim assump_217
            case inr assump_196 =>
              cases assump_196
              case intro assump_222 assump_223 =>
                cases assump_192
                case intro assump_228 assump_229 =>
                  cases assump_229
                  case inl assump_232 =>
                    have assump_290 : (p5 → True) := by
                      intro assump_239
                      apply True.intro
                    let assump_238 := assump_228 assump_290
                    apply False.elim assump_238
                  case inr assump_233 =>
                    have assump_291 : (p5 → True) := by
                      intro assump_247
                      apply True.intro
                    let assump_246 := assump_228 assump_291
                    apply False.elim assump_246
          case inr assump_194 =>
            cases assump_192
            case intro assump_253 assump_254 =>
              cases assump_254
              case inl assump_257 =>
                have assump_292 : (p5 → True) := by
                  intro assump_264
                  apply True.intro
                let assump_263 := assump_253 assump_292
                apply False.elim assump_263
              case inr assump_258 =>
                have assump_293 : (p5 → True) := by
                  intro assump_272
                  apply True.intro
                let assump_271 := assump_253 assump_293
                apply False.elim assump_271


variable (p3 p0 p5 p1 : Prop)
theorem file17_71305 : (((((p5 ∧ p0) ∨ (p3 ∨ p0)) ∨ ((p3 ∧ p5) → (p0 → p1))) → False) → ((((p0 → p5) → False) → False) ∧ (((True → False) ∧ (p0 → False)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_58 : (((p5 ∧ p0) ∨ (p3 ∨ p0)) ∨ ((p3 ∧ p5) → (p0 → p1))) := by
    apply Or.inr
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      have assump_59 : (((p5 ∧ p0) ∨ (p3 ∨ p0)) ∨ ((p3 ∧ p5) → (p0 → p1))) := by
        apply Or.inl
        apply Or.inl
        apply And.intro
        exact assump_13
        exact assump_9
      let assump_21 := assump_1 assump_59
      apply False.elim assump_21
  let assump_7 := assump_1 assump_58
  apply False.elim assump_7
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    have assump_60 : (((p5 ∧ p0) ∨ (p3 ∨ p0)) ∨ ((p3 ∧ p5) → (p0 → p1))) := by
      apply Or.inr
      intro assump_38
      intro assump_39
      cases assump_38
      case intro assump_42 assump_43 =>
        have assump_61 : (((p5 ∧ p0) ∨ (p3 ∨ p0)) ∨ ((p3 ∧ p5) → (p0 → p1))) := by
          apply Or.inl
          apply Or.inl
          apply And.intro
          exact assump_43
          exact assump_39
        let assump_51 := assump_1 assump_61
        apply False.elim assump_51
    let assump_37 := assump_1 assump_60
    apply False.elim assump_37


variable (p5 p1 p6 p2 p0 p7 : Prop)
theorem file17_72721 : ((((((False ∧ p5) → (p6 → p7)) ∨ ((p6 ∨ True) → (p5 → p7))) → (((p2 → p2) ∧ (p0 ∨ p5)) → ((p1 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((False ∧ p5) → (p6 → p7)) ∨ ((p6 ∨ True) → (p5 → p7))) → (((p2 → p2) ∧ (p0 ∨ p5)) → ((p1 ∧ False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p4 p6 p5 p7 p0 p2 p1 : Prop)
theorem file17_73285 : ((((((p6 ∧ p4) → (True → False)) ∧ ((p7 → False) ∨ (p7 ∧ False))) ∧ (((False → p2) ∨ (p5 → p1)) ∧ ((p2 → p6) ∧ (p6 ∧ False)))) ∧ ((((p0 ∨ p7) ∧ (p1 ∧ p6)) → False) ∨ (((p1 → p7) → (p7 → True)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          cases assump_9
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_19
              case intro assump_24 assump_25 =>
                cases assump_25
                case intro assump_28 assump_29 =>
                  apply False.elim assump_29
            case inr assump_21 =>
              cases assump_19
              case intro assump_36 assump_37 =>
                cases assump_37
                case intro assump_40 assump_41 =>
                  apply False.elim assump_41
        case inr assump_15 =>
          cases assump_15
          case intro assump_46 assump_47 =>
            apply False.elim assump_47


variable (p6 p7 p2 p0 p5 p1 p4 : Prop)
theorem file17_74519 : ((((((p1 → False) ∧ (p0 → False)) → False) → False) ∧ ((((p6 → p7) ∨ (p4 ∧ p0)) ∨ ((p0 ∧ p7) ∨ (p4 ∧ p0))) ∧ (((p5 ∧ p0) ∧ (p6 ∨ p2)) ∧ ((False → True) → False)))) → False) := by
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
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_17
                case inl assump_24 =>
                  have assump_154 : (False → True) := by
                    intro assump_31
                    apply True.intro
                  let assump_30 := assump_15 assump_154
                  apply False.elim assump_30
                case inr assump_25 =>
                  have assump_155 : (False → True) := by
                    intro assump_40
                    apply True.intro
                  let assump_39 := assump_15 assump_155
                  apply False.elim assump_39
        case inr assump_11 =>
          cases assump_11
          case intro assump_44 assump_45 =>
            cases assump_7
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_52
                case intro assump_54 assump_55 =>
                  cases assump_53
                  case inl assump_60 =>
                    have assump_156 : (False → True) := by
                      intro assump_67
                      apply True.intro
                    let assump_66 := assump_51 assump_156
                    apply False.elim assump_66
                  case inr assump_61 =>
                    have assump_157 : (False → True) := by
                      intro assump_76
                      apply True.intro
                    let assump_75 := assump_51 assump_157
                    apply False.elim assump_75
      case inr assump_9 =>
        cases assump_9
        case inl assump_80 =>
          cases assump_80
          case intro assump_82 assump_83 =>
            cases assump_7
            case intro assump_88 assump_89 =>
              cases assump_88
              case intro assump_90 assump_91 =>
                cases assump_90
                case intro assump_92 assump_93 =>
                  cases assump_91
                  case inl assump_98 =>
                    have assump_158 : (False → True) := by
                      intro assump_105
                      apply True.intro
                    let assump_104 := assump_89 assump_158
                    apply False.elim assump_104
                  case inr assump_99 =>
                    have assump_159 : (False → True) := by
                      intro assump_114
                      apply True.intro
                    let assump_113 := assump_89 assump_159
                    apply False.elim assump_113
        case inr assump_81 =>
          cases assump_81
          case intro assump_118 assump_119 =>
            cases assump_7
            case intro assump_124 assump_125 =>
              cases assump_124
              case intro assump_126 assump_127 =>
                cases assump_126
                case intro assump_128 assump_129 =>
                  cases assump_127
                  case inl assump_134 =>
                    have assump_160 : (False → True) := by
                      intro assump_141
                      apply True.intro
                    let assump_140 := assump_125 assump_160
                    apply False.elim assump_140
                  case inr assump_135 =>
                    have assump_161 : (False → True) := by
                      intro assump_150
                      apply True.intro
                    let assump_149 := assump_125 assump_161
                    apply False.elim assump_149


variable (p2 p1 p5 p6 p3 p4 : Prop)
theorem file17_78637 : (((((p2 ∨ p4) ∧ (True → False)) ∧ ((p1 ∧ p3) ∨ (p1 → p5))) → False) ∨ ((((p5 ∧ p1) → False) → False) → (((p6 → False) ∨ (True ∧ p4)) → False))) := by
  apply Or.inl
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
          case intro assump_14 assump_15 =>
            have assump_58 : True := by
              apply True.intro
            let assump_22 := assump_5 assump_58
            apply False.elim assump_22
        case inr assump_13 =>
          have assump_59 : True := by
            apply True.intro
          let assump_29 := assump_5 assump_59
          apply False.elim assump_29
      case inr assump_7 =>
        cases assump_3
        case inl assump_37 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            have assump_60 : True := by
              apply True.intro
            let assump_47 := assump_5 assump_60
            apply False.elim assump_47
        case inr assump_38 =>
          have assump_61 : True := by
            apply True.intro
          let assump_54 := assump_5 assump_61
          apply False.elim assump_54


variable (p3 p0 p6 p4 p5 : Prop)
theorem file17_79979 : (((((True → False) → False) ∨ ((True ∨ True) → (p3 → False))) ∨ (((p3 → False) → False) → ((p4 ∨ False) → False))) ∨ ((((p6 → False) → False) → False) ∧ (((p6 → p0) → (p5 → p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p5 p2 p3 p6 p4 p7 p0 : Prop)
theorem file17_80413 : (((((p5 ∧ p0) ∧ (p0 → False)) → False) ∨ (((p3 → p6) → (p5 ∨ p0)) → False)) ∨ ((((p3 → p6) ∨ (p4 ∧ p0)) ∧ ((False → p7) → False)) ∧ (((p0 ∧ p2) → (False ∧ True)) ∧ ((p3 → p5) ∨ (p0 ∧ p2))))) := by
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


variable (p7 p5 p2 p1 p4 p0 p3 : Prop)
theorem file17_80956 : (((((p0 ∨ p7) → (p2 → p5)) → ((p0 → False) → (p3 → True))) → (((p4 → False) → (False → False)) ∨ ((p2 → p7) ∨ (p3 → False)))) ∨ ((((p4 → p4) → False) ∨ ((p4 → False) → (p5 → False))) ∨ (((p1 → False) ∧ (p7 ∨ p4)) ∧ ((p3 → False) → (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p0 p1 p4 p3 p6 p5 p2 : Prop)
theorem file17_81382 : (((((p6 → False) → False) → False) ∧ (((p0 → p5) → False) ∧ ((p2 → p4) ∨ (p2 → p2)))) → ((((p2 ∨ False) ∨ (p1 ∨ p5)) → ((False ∧ p6) ∨ (True ∨ p3))) ∨ (((p3 ∧ p0) → (p5 ∨ p6)) ∨ ((True → False) ∨ (p2 → p2))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case inl assump_15 =>
          cases assump_15
          case inl assump_17 =>
            apply Or.inr
            apply Or.inl
            apply True.intro
          case inr assump_18 =>
            apply False.elim assump_18
        case inr assump_16 =>
          cases assump_16
          case inl assump_23 =>
            apply Or.inr
            apply Or.inl
            apply True.intro
          case inr assump_24 =>
            apply Or.inr
            apply Or.inl
            apply True.intro
      case inr assump_11 =>
        apply Or.inl
        intro assump_31
        cases assump_31
        case inl assump_32 =>
          cases assump_32
          case inl assump_34 =>
            apply Or.inr
            apply Or.inl
            apply True.intro
          case inr assump_35 =>
            apply False.elim assump_35
        case inr assump_33 =>
          cases assump_33
          case inl assump_40 =>
            apply Or.inr
            apply Or.inl
            apply True.intro
          case inr assump_41 =>
            apply Or.inr
            apply Or.inl
            apply True.intro


variable (p2 p5 p1 p6 p3 p4 p7 : Prop)
theorem file17_83031 : ((((((p3 ∧ p7) → (p5 → False)) ∨ ((p6 ∨ p1) ∧ (True → p6))) ∨ (((p3 → False) ∨ (p2 → False)) → ((p1 ∨ p3) ∨ (False → p4)))) ∧ ((((p2 → p3) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_144 : (((p2 → p3) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → p4))) := by
          intro assump_13
          cases assump_13
          case intro assump_14 assump_15 =>
            apply Or.inr
            intro assump_20
            have assump_145 : (((p2 → p3) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → p4))) := by
              intro assump_27
              cases assump_27
              case intro assump_28 assump_29 =>
                apply Or.inl
                apply Or.inr
                exact assump_20
            let assump_26 := assump_3 assump_145
            apply False.elim assump_26
        let assump_12 := assump_3 assump_144
        apply False.elim assump_12
      case inr assump_7 =>
        cases assump_7
        case intro assump_40 assump_41 =>
          cases assump_40
          case inl assump_42 =>
            have assump_146 : (((p2 → p3) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → p4))) := by
              intro assump_51
              cases assump_51
              case intro assump_52 assump_53 =>
                apply Or.inr
                intro assump_58
                have assump_147 : (((p2 → p3) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → p4))) := by
                  intro assump_65
                  cases assump_65
                  case intro assump_66 assump_67 =>
                    apply Or.inl
                    apply Or.inr
                    exact assump_58
                let assump_64 := assump_3 assump_147
                apply False.elim assump_64
            let assump_50 := assump_3 assump_146
            apply False.elim assump_50
          case inr assump_43 =>
            have assump_148 : (((p2 → p3) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → p4))) := by
              intro assump_85
              cases assump_85
              case intro assump_86 assump_87 =>
                apply Or.inr
                intro assump_92
                have assump_149 : (((p2 → p3) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → p4))) := by
                  intro assump_99
                  cases assump_99
                  case intro assump_100 assump_101 =>
                    apply Or.inl
                    apply Or.inr
                    exact assump_92
                let assump_98 := assump_3 assump_149
                apply False.elim assump_98
            let assump_84 := assump_3 assump_148
            apply False.elim assump_84
    case inr assump_5 =>
      have assump_150 : (((p2 → p3) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → p4))) := by
        intro assump_117
        cases assump_117
        case intro assump_118 assump_119 =>
          apply Or.inr
          intro assump_124
          have assump_151 : (((p2 → p3) ∧ (p3 → False)) → ((p7 ∨ p5) ∨ (p5 → p4))) := by
            intro assump_131
            cases assump_131
            case intro assump_132 assump_133 =>
              apply Or.inl
              apply Or.inr
              exact assump_124
          let assump_130 := assump_3 assump_151
          apply False.elim assump_130
      let assump_116 := assump_3 assump_150
      apply False.elim assump_116


variable (p3 p1 p5 p0 p4 p2 : Prop)
theorem file17_86555 : (((((p2 ∨ p4) ∨ (p5 ∨ True)) → False) → (((p0 ∧ False) ∧ (p0 → False)) ∧ ((p5 ∧ p0) ∨ (p3 → True)))) ∨ ((((p5 ∧ p2) → False) → False) → (((True ∨ True) ∨ (p3 → p1)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  have assump_26 : ((p2 ∨ p4) ∨ (p5 ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4
  have assump_27 : ((p2 ∨ p4) ∨ (p5 ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_10 := assump_1 assump_27
  apply False.elim assump_10
  intro assump_14
  have assump_28 : ((p2 ∨ p4) ∨ (p5 ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_19 := assump_1 assump_28
  apply False.elim assump_19
  apply Or.inr
  intro assump_25
  apply True.intro


variable (p6 p7 p3 p1 : Prop)
theorem file17_87464 : (((((p3 ∨ p6) → False) ∧ ((False → False) → False)) ∧ (((p1 → False) ∨ (p6 → p3)) ∧ ((p7 → True) ∧ (p7 → False)))) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_13
      case intro assump_20 assump_21 =>
        cases assump_20
        case inl assump_22 =>
          cases assump_21
          case intro assump_26 assump_27 =>
            have assump_60 : (False → False) := by
              intro assump_36
              apply False.elim assump_36
            let assump_35 := assump_15 assump_60
            apply False.elim assump_35
        case inr assump_23 =>
          cases assump_21
          case intro assump_44 assump_45 =>
            have assump_61 : (False → False) := by
              intro assump_54
              apply False.elim assump_54
            let assump_53 := assump_15 assump_61
            apply False.elim assump_53


variable (p7 p3 p0 p5 p4 p2 p6 p1 : Prop)
theorem file17_88496 : (((((p3 ∧ p1) ∨ (p7 ∨ False)) ∨ ((p3 ∨ p4) ∧ (p1 → False))) → (((p6 ∧ p2) ∨ (p0 → p1)) → ((p5 ∧ p0) ∨ (p7 → True)))) ∨ ((((p6 ∨ p2) ∧ (p6 ∨ p4)) → ((p4 ∧ p4) → False)) ∨ (((True → p4) → False) ∨ ((p5 ∧ p0) → (p7 → p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            apply Or.inr
            intro assump_21
            apply True.intro
        case inr assump_14 =>
          cases assump_14
          case inl assump_22 =>
            apply Or.inr
            intro assump_26
            apply True.intro
          case inr assump_23 =>
            apply False.elim assump_23
      case inr assump_12 =>
        cases assump_12
        case intro assump_29 assump_30 =>
          cases assump_29
          case inl assump_31 =>
            apply Or.inr
            intro assump_37
            apply True.intro
          case inr assump_32 =>
            apply Or.inr
            intro assump_42
            apply True.intro
  case inr assump_4 =>
    cases assump_1
    case inl assump_45 =>
      cases assump_45
      case inl assump_47 =>
        cases assump_47
        case intro assump_49 assump_50 =>
          apply Or.inr
          intro assump_55
          apply True.intro
      case inr assump_48 =>
        cases assump_48
        case inl assump_56 =>
          apply Or.inr
          intro assump_60
          apply True.intro
        case inr assump_57 =>
          apply False.elim assump_57
    case inr assump_46 =>
      cases assump_46
      case intro assump_63 assump_64 =>
        cases assump_63
        case inl assump_65 =>
          apply Or.inr
          intro assump_71
          apply True.intro
        case inr assump_66 =>
          apply Or.inr
          intro assump_76
          apply True.intro


variable (p2 p3 p1 p5 p6 : Prop)
theorem file17_90578 : ((((((p5 ∧ False) ∧ (p3 → False)) → ((p1 → False) ∧ (p6 → p1))) ∨ (((p5 ∨ False) → False) ∧ ((p1 → False) → (p2 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p5 ∧ False) ∧ (p3 → False)) → ((p1 → False) ∧ (p6 → p1))) ∨ (((p5 ∨ False) → False) ∧ ((p1 → False) → (p2 ∨ p1)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    intro assump_17
    cases assump_5
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        apply False.elim assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p6 p2 p1 p5 p0 p4 p3 : Prop)
theorem file17_91413 : (((((p2 ∧ False) → (p0 ∨ p6)) ∧ ((p3 ∧ p1) ∧ (p3 ∧ False))) → (((p2 ∧ p0) ∧ (False → False)) ∨ ((p0 ∨ p6) ∧ (p1 → False)))) ∨ ((((p5 ∨ p2) → (False → False)) ∧ ((p6 → p0) ∧ (p6 ∧ p1))) → (((p2 → p5) ∨ (p1 ∨ p5)) ∨ ((p3 → False) → (False ∧ p4))))) := by
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


variable (p7 p6 p2 p3 p4 p1 : Prop)
theorem file17_92025 : (((((False ∧ p3) → (p6 ∨ p7)) → ((p4 ∨ p4) → (p2 → p3))) → False) → ((((p1 ∧ p3) → (p1 → False)) ∨ ((True → p4) ∨ (False → False))) ∨ (((p3 ∨ p7) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    have assump_36 : (((False ∧ p3) → (p6 ∨ p7)) → ((p4 ∨ p4) → (p2 → p3))) := by
      intro assump_18
      intro assump_19
      intro assump_20
      cases assump_19
      case inl assump_23 =>
        exact assump_9
      case inr assump_24 =>
        exact assump_9
    let assump_17 := assump_1 assump_36
    apply False.elim assump_17


variable (p2 p6 p4 : Prop)
theorem file17_92723 : ((((((p4 ∧ p4) → (p2 → p6)) ∧ ((p4 → False) ∧ (True → False))) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p4 ∧ p4) → (p2 → p6)) ∧ ((p4 → False) ∧ (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_11 assump_24
        apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p0 p1 p7 p4 p6 p3 p5 p2 : Prop)
theorem file17_93340 : ((((((False → p5) ∨ (p0 → False)) ∧ ((p4 → p7) → (p6 ∧ True))) ∨ (((p0 → p2) ∧ (False → True)) ∨ ((p1 → False) → False))) ∧ ((((p3 → False) ∨ (p5 ∨ p1)) → ((p7 ∧ p0) → (p5 ∧ p2))) ∧ (((p1 ∨ False) → False) ∧ ((True → False) ∧ (p7 ∧ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  have assump_124 : True := by
                    apply True.intro
                  let assump_34 := assump_22 assump_124
                  apply False.elim assump_34
        case inr assump_9 =>
          cases assump_3
          case intro assump_42 assump_43 =>
            cases assump_43
            case intro assump_46 assump_47 =>
              cases assump_47
              case intro assump_50 assump_51 =>
                cases assump_51
                case intro assump_54 assump_55 =>
                  have assump_125 : True := by
                    apply True.intro
                  let assump_62 := assump_50 assump_125
                  apply False.elim assump_62
    case inr assump_5 =>
      cases assump_5
      case inl assump_66 =>
        cases assump_66
        case intro assump_68 assump_69 =>
          cases assump_3
          case intro assump_74 assump_75 =>
            cases assump_75
            case intro assump_78 assump_79 =>
              cases assump_79
              case intro assump_82 assump_83 =>
                cases assump_83
                case intro assump_86 assump_87 =>
                  have assump_126 : True := by
                    apply True.intro
                  let assump_94 := assump_82 assump_126
                  apply False.elim assump_94
      case inr assump_67 =>
        cases assump_3
        case intro assump_100 assump_101 =>
          cases assump_101
          case intro assump_104 assump_105 =>
            cases assump_105
            case intro assump_108 assump_109 =>
              cases assump_109
              case intro assump_112 assump_113 =>
                have assump_127 : True := by
                  apply True.intro
                let assump_120 := assump_108 assump_127
                apply False.elim assump_120


variable (p7 p2 p1 p4 : Prop)
theorem file17_96011 : ((((((p1 → False) ∧ (p7 ∧ p2)) ∧ ((p2 ∨ True) → False)) → False) ∧ ((((True → p7) ∧ (False ∧ p4)) → ((False → p2) → (p1 ∨ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((True → p7) ∧ (False ∧ p4)) → ((False → p2) → (p1 ∨ p4))) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p6 p1 p5 : Prop)
theorem file17_96646 : ((((((True → False) ∧ (p1 ∧ p6)) → False) ∨ (((p1 ∨ p5) → False) → ((p1 ∧ True) → (p1 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → False) ∧ (p1 ∧ p6)) → False) ∨ (((p1 ∨ p5) → False) → ((p1 ∧ True) → (p1 ∨ p6)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : True := by
          apply True.intro
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p4 p5 p6 p2 p3 p0 : Prop)
theorem file17_97319 : ((((((p2 → False) → False) ∨ ((p6 → False) ∨ (p6 → p6))) → False) ∧ ((((p5 → p6) ∧ (p3 → False)) ∧ ((False → p3) → False)) ∧ (((p6 ∧ p4) → False) ∨ ((p0 → p2) ∨ (p2 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case inl assump_18 =>
            have assump_52 : (False → p3) := by
              intro assump_24
              apply False.elim assump_24
            let assump_23 := assump_9 assump_52
            apply False.elim assump_23
          case inr assump_19 =>
            cases assump_19
            case inl assump_30 =>
              have assump_53 : (False → p3) := by
                intro assump_36
                apply False.elim assump_36
              let assump_35 := assump_9 assump_53
              apply False.elim assump_35
            case inr assump_31 =>
              have assump_54 : (False → p3) := by
                intro assump_46
                apply False.elim assump_46
              let assump_45 := assump_9 assump_54
              apply False.elim assump_45


variable (p5 p4 p2 p7 p0 p6 : Prop)
theorem file17_98642 : ((((((p6 → p2) ∧ (p6 → p7)) → ((p2 → p0) → False)) ∨ (((False ∧ True) → (False → False)) → False)) ∧ ((((False ∨ True) → False) → ((p7 → False) ∧ (p4 ∨ p5))) → False)) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case inl assump_17 =>
      have assump_67 : (((False ∨ True) → False) → ((p7 → False) ∧ (p4 ∨ p5))) := by
        intro assump_24
        apply And.intro
        intro assump_25
        have assump_68 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_30 := assump_24 assump_68
        apply False.elim assump_30
        have assump_69 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_36 := assump_24 assump_69
        apply False.elim assump_36
      let assump_23 := assump_16 assump_67
      apply False.elim assump_23
    case inr assump_18 =>
      have assump_70 : (((False ∨ True) → False) → ((p7 → False) ∧ (p4 ∨ p5))) := by
        intro assump_48
        apply And.intro
        intro assump_49
        have assump_71 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_54 := assump_48 assump_71
        apply False.elim assump_54
        have assump_72 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_60 := assump_48 assump_72
        apply False.elim assump_60
      let assump_47 := assump_16 assump_70
      apply False.elim assump_47


variable (p5 p0 p7 p2 p3 p1 p4 : Prop)
theorem file17_100202 : ((((((p4 → False) ∨ (p5 → p4)) ∧ ((p1 → False) ∧ (False ∧ False))) ∧ (((p4 → False) ∨ (p1 ∨ p1)) ∨ ((p3 ∧ p7) ∨ (False → True)))) ∧ ((((p0 → True) ∨ (p2 → False)) → ((p7 ∧ False) → (True → p2))) ∨ (((p5 ∧ p0) ∧ (p3 → p1)) ∨ ((p4 → p5) → False)))) → False) := by
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
            cases assump_13
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
        case inr assump_9 =>
          cases assump_7
          case intro assump_22 assump_23 =>
            cases assump_23
            case intro assump_26 assump_27 =>
              apply False.elim assump_26


variable (p3 p7 p0 p1 p2 p6 : Prop)
theorem file17_101155 : (((((True → False) ∧ (False → False)) ∨ ((p2 → p7) → False)) → (((p0 ∧ False) ∧ (p6 ∧ p0)) → False)) ∨ ((((p0 ∧ False) → False) → False) ∧ (((p1 ∧ p0) ∧ (False ∨ p7)) ∨ ((p0 ∧ p6) ∧ (p1 → p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6


variable (p6 p7 p3 p4 p2 p1 p5 p0 : Prop)
theorem file17_101610 : (((((p3 ∨ p0) ∨ (p5 ∧ p6)) → ((p6 ∧ p3) → (True → False))) → (((p5 → False) → (p2 → False)) → ((p4 ∨ True) ∨ (p0 → p6)))) ∨ ((((p1 → False) → (False → False)) → ((True → False) ∧ (p1 → p2))) → (((p4 → False) → (p4 ∧ p7)) ∨ ((True ∨ p0) ∧ (p0 ∨ p2))))) := by
  apply Or.inl
  intro assump_6
  intro assump_7
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p3 p2 p6 p7 p4 p0 p5 p1 : Prop)
theorem file17_102032 : ((((((p4 ∧ True) ∧ (False ∧ p7)) ∨ ((p6 ∨ p1) → False)) ∨ (((False ∨ p0) → (p7 ∨ p6)) ∨ ((False ∧ p3) ∨ (p3 ∨ p5)))) ∧ ((((False → False) ∨ (p2 → False)) ∨ ((p7 → False) → (False ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_9
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
      case inr assump_7 =>
        have assump_74 : (((False → False) ∨ (p2 → False)) ∨ ((p7 → False) → (False ∨ True))) := by
          apply Or.inl
          apply Or.inl
          intro assump_25
          apply False.elim assump_25
        let assump_24 := assump_3 assump_74
        apply False.elim assump_24
    case inr assump_5 =>
      cases assump_5
      case inl assump_31 =>
        have assump_75 : (((False → False) ∨ (p2 → False)) ∨ ((p7 → False) → (False ∨ True))) := by
          apply Or.inl
          apply Or.inl
          intro assump_38
          apply False.elim assump_38
        let assump_37 := assump_3 assump_75
        apply False.elim assump_37
      case inr assump_32 =>
        cases assump_32
        case inl assump_44 =>
          cases assump_44
          case intro assump_46 assump_47 =>
            apply False.elim assump_46
        case inr assump_45 =>
          cases assump_45
          case inl assump_50 =>
            have assump_76 : (((False → False) ∨ (p2 → False)) ∨ ((p7 → False) → (False ∨ True))) := by
              apply Or.inl
              apply Or.inl
              intro assump_57
              apply False.elim assump_57
            let assump_56 := assump_3 assump_76
            apply False.elim assump_56
          case inr assump_51 =>
            have assump_77 : (((False → False) ∨ (p2 → False)) ∨ ((p7 → False) → (False ∨ True))) := by
              apply Or.inl
              apply Or.inl
              intro assump_68
              apply False.elim assump_68
            let assump_67 := assump_3 assump_77
            apply False.elim assump_67


variable (p5 p4 p1 : Prop)
theorem file17_104323 : ((((((p4 ∨ p1) → False) → ((False ∧ True) → False)) → False) ∧ ((((p5 ∧ p1) → False) → ((False → p5) ∧ (p4 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p5 ∧ p1) → False) → ((False → p5) ∧ (p4 → True))) := by
      intro assump_9
      apply And.intro
      intro assump_10
      apply False.elim assump_10
      intro assump_13
      apply True.intro
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p6 p0 p3 p5 : Prop)
theorem file17_104879 : (((((p5 ∧ p0) ∨ (True ∧ True)) ∨ ((p3 ∧ p6) ∧ (False → False))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p5 ∧ p0) ∨ (True ∧ True)) ∨ ((p3 ∧ p6) ∧ (False → False))) := by
    apply Or.inl
    apply Or.inr
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p6 p7 p4 p0 p5 p3 : Prop)
theorem file17_105293 : (((((False ∧ p4) → (p3 ∨ p4)) → False) → (((p1 ∧ p6) → False) → ((p7 ∧ False) → (p3 ∨ p4)))) ∨ ((((p1 → p1) ∧ (p0 → p7)) → False) ∨ (((p1 ∧ p5) ∧ (p1 → False)) ∧ ((p7 ∧ p0) ∧ (False ∨ p1))))) := by
  apply Or.inl
  intro assump_13
  intro assump_14
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    apply False.elim assump_17


variable (p1 p0 p3 p5 p2 : Prop)
theorem file17_105702 : ((((((p3 → p5) → (p0 ∨ True)) → False) ∧ (((p1 ∧ p0) ∨ (p0 ∧ p3)) → False)) ∧ ((((p0 ∨ p3) ∨ (p1 ∧ p2)) → False) ∨ (((p2 ∧ p5) → (p5 ∨ True)) ∧ ((True → p3) ∧ (p1 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        have assump_37 : ((p3 → p5) → (p0 ∨ True)) := by
          intro assump_17
          apply Or.inr
          apply True.intro
        let assump_16 := assump_4 assump_37
        apply False.elim assump_16
      case inr assump_11 =>
        cases assump_11
        case intro assump_23 assump_24 =>
          cases assump_24
          case intro assump_27 assump_28 =>
            cases assump_28
            case intro assump_31 assump_32 =>
              apply False.elim assump_32


variable (p7 p2 p0 p3 p5 : Prop)
theorem file17_106613 : (((((p7 → False) → (False → False)) → False) → False) ∨ ((((p2 → p2) ∨ (p0 → False)) ∧ ((p7 → False) ∨ (p3 → p5))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p7 → False) → (False → False)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p3 p6 p4 p7 p1 : Prop)
theorem file17_107027 : ((((((False ∨ p4) → False) → False) → (((p6 ∨ p7) ∧ (p1 ∧ p3)) ∨ ((p5 → p3) → (p6 → False)))) ∧ ((((p4 ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p4 ∨ True) → False) → False) := by
      intro assump_9
      have assump_20 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p6 p3 p1 : Prop)
theorem file17_107611 : (((((p6 ∧ False) ∧ (p3 → p1)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((p6 ∧ False) ∧ (p3 → p1)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p4 p2 : Prop)
theorem file17_108036 : ((((((True → False) → False) → False) → (((p7 → p4) ∧ (p2 ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_33 : ((((True → False) → False) → False) → (((p7 → p4) ∧ (p2 ∧ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_34 : ((True → False) → False) := by
          intro assump_20
          have assump_35 : True := by
            apply True.intro
          let assump_23 := assump_20 assump_35
          apply False.elim assump_23
        let assump_19 := assump_5 assump_34
        apply False.elim assump_19
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p7 p0 p3 p1 p4 p6 p2 : Prop)
theorem file17_108844 : (((((p3 ∨ False) → (p4 → p0)) ∧ ((p3 ∧ True) → (p4 ∧ p3))) ∨ (((p2 ∨ p7) ∨ (p3 ∨ p6)) ∨ ((p1 ∧ p2) → False))) → ((((True → True) ∧ (True ∨ p6)) ∨ ((p3 ∧ True) → False)) ∨ (((p1 ∨ p0) ∨ (p1 → False)) ∨ ((p0 ∨ True) ∧ (p2 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inl
      apply And.intro
      intro assump_10
      apply True.intro
      apply Or.inl
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          apply Or.inl
          apply Or.inl
          apply And.intro
          intro assump_19
          apply True.intro
          apply Or.inl
          apply True.intro
        case inr assump_16 =>
          apply Or.inl
          apply Or.inl
          apply And.intro
          intro assump_22
          apply True.intro
          apply Or.inl
          apply True.intro
      case inr assump_14 =>
        cases assump_14
        case inl assump_23 =>
          apply Or.inl
          apply Or.inl
          apply And.intro
          intro assump_27
          apply True.intro
          apply Or.inl
          apply True.intro
        case inr assump_24 =>
          apply Or.inl
          apply Or.inl
          apply And.intro
          intro assump_30
          apply True.intro
          apply Or.inl
          apply True.intro
    case inr assump_12 =>
      apply Or.inl
      apply Or.inl
      apply And.intro
      intro assump_33
      apply True.intro
      apply Or.inl
      apply True.intro


variable (p6 p7 p0 p5 p2 p1 : Prop)
theorem file17_110589 : (((((p1 ∧ p5) → False) → False) ∧ (((True ∧ p7) ∨ (p6 → p1)) ∨ ((p0 → p1) → False))) → ((((p1 → False) ∧ (p0 → False)) → ((p0 → False) → False)) ∨ (((False ∧ p5) ∧ (p2 → False)) → ((p1 → p2) ∧ (p5 → p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_16
          intro assump_17
          cases assump_16
          case intro assump_20 assump_21 =>
            have assump_109 : ((p1 ∧ p5) → False) := by
              intro assump_31
              cases assump_31
              case intro assump_32 assump_33 =>
                have assump_110 : p1 := by
                  exact assump_32
                let assump_41 := assump_20 assump_110
                apply False.elim assump_41
            let assump_30 := assump_2 assump_109
            apply False.elim assump_30
      case inr assump_9 =>
        apply Or.inl
        intro assump_50
        intro assump_51
        cases assump_50
        case intro assump_54 assump_55 =>
          have assump_111 : ((p1 ∧ p5) → False) := by
            intro assump_65
            cases assump_65
            case intro assump_66 assump_67 =>
              have assump_112 : p1 := by
                exact assump_66
              let assump_75 := assump_54 assump_112
              apply False.elim assump_75
          let assump_64 := assump_2 assump_111
          apply False.elim assump_64
    case inr assump_7 =>
      apply Or.inl
      intro assump_84
      intro assump_85
      cases assump_84
      case intro assump_88 assump_89 =>
        have assump_113 : (p0 → p1) := by
          intro assump_98
          have assump_114 : p0 := by
            exact assump_98
          let assump_102 := assump_89 assump_114
          apply False.elim assump_102
        let assump_97 := assump_7 assump_113
        apply False.elim assump_97


variable (p5 p7 p6 p1 p4 p2 : Prop)
theorem file17_112676 : (((((p6 ∧ p7) ∧ (p7 ∧ p6)) ∨ ((True ∧ False) ∧ (p2 → False))) ∧ (((p6 → False) → (p5 → p5)) → False)) → ((((True ∨ True) ∨ (p1 ∧ p7)) → False) ∨ (((True → False) ∧ (False ∧ p4)) → False))) := by
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    cases assump_31
    case inl assump_33 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        cases assump_35
        case intro assump_37 assump_38 =>
          cases assump_36
          case intro assump_43 assump_44 =>
            apply Or.inl
            intro assump_51
            cases assump_51
            case inl assump_52 =>
              cases assump_52
              case inl assump_54 =>
                have assump_106 : ((p6 → False) → (p5 → p5)) := by
                  intro assump_59
                  intro assump_60
                  exact assump_60
                let assump_58 := assump_32 assump_106
                apply False.elim assump_58
              case inr assump_55 =>
                have assump_107 : ((p6 → False) → (p5 → p5)) := by
                  intro assump_71
                  intro assump_72
                  exact assump_72
                let assump_70 := assump_32 assump_107
                apply False.elim assump_70
            case inr assump_53 =>
              cases assump_53
              case intro assump_80 assump_81 =>
                have assump_108 : ((p6 → False) → (p5 → p5)) := by
                  intro assump_89
                  intro assump_90
                  exact assump_90
                let assump_88 := assump_32 assump_108
                apply False.elim assump_88
    case inr assump_34 =>
      cases assump_34
      case intro assump_98 assump_99 =>
        cases assump_98
        case intro assump_100 assump_101 =>
          apply False.elim assump_101


variable (p7 p4 p3 p5 p0 p1 p6 : Prop)
theorem file17_114571 : (((((p6 ∨ p1) ∧ (p1 ∧ p6)) ∧ ((p7 ∧ p7) ∧ (True → False))) → False) ∨ ((((p1 → False) → (True → False)) → ((p1 ∧ p7) → False)) ∧ (((False ∨ p3) ∧ (p7 → False)) → ((p0 → p5) ∨ (p4 → False))))) := by
  apply Or.inl
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    cases assump_29
    case intro assump_31 assump_32 =>
      cases assump_31
      case inl assump_33 =>
        cases assump_32
        case intro assump_37 assump_38 =>
          cases assump_30
          case intro assump_43 assump_44 =>
            cases assump_43
            case intro assump_45 assump_46 =>
              have assump_79 : True := by
                apply True.intro
              let assump_53 := assump_44 assump_79
              apply False.elim assump_53
      case inr assump_34 =>
        cases assump_32
        case intro assump_59 assump_60 =>
          cases assump_30
          case intro assump_65 assump_66 =>
            cases assump_65
            case intro assump_67 assump_68 =>
              have assump_80 : True := by
                apply True.intro
              let assump_75 := assump_66 assump_80
              apply False.elim assump_75


variable (p4 p6 p7 p1 p2 p3 : Prop)
theorem file17_115806 : ((((((p4 ∧ p3) → False) ∧ ((p2 ∧ p2) → (p6 ∧ False))) → (((True ∧ p1) ∧ (p7 → p1)) → ((p7 → p2) → (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p4 ∧ p3) → False) ∧ ((p2 ∧ p2) → (p6 ∧ False))) → (((True ∧ p1) ∧ (p7 → p1)) → ((p7 → p2) → (p2 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_6
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_5
        case intro assump_23 assump_24 =>
          have assump_39 : (p2 ∧ p2) := by
            apply And.intro
            exact assump_8
            exact assump_8
          let assump_29 := assump_24 assump_39
          let assump_30 := And.right assump_29
          apply False.elim assump_30
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p1 p3 p6 p5 p2 p4 p0 p7 : Prop)
theorem file17_116745 : (((((False → p7) ∨ (p5 → False)) ∨ ((p6 ∧ p6) → (p2 ∧ p3))) ∧ (((p3 ∨ p2) ∨ (False → False)) ∨ ((True ∧ p1) → False))) ∨ ((((p4 → p0) ∧ (p3 ∧ p5)) ∨ ((p5 ∧ False) ∧ (p0 ∨ p2))) → (((p5 → p6) ∧ (p6 → False)) → False))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


