variable (p6 p1 p0 p5 p7 : Prop)
theorem file46_41 : (((((p7 → p1) → False) ∧ ((p7 → False) ∨ (p7 ∧ False))) → False) ∧ ((((False → p0) ∨ (p1 → False)) ∨ ((p6 ∧ False) → False)) ∨ (((p1 → p5) ∨ (p5 → p7)) ∨ ((p5 ∨ True) → False)))) := by
  apply And.intro
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    cases assump_33
    case inl assump_36 =>
      have assump_62 : (p7 → p1) := by
        intro assump_42
        have assump_63 : p7 := by
          exact assump_42
        let assump_46 := assump_36 assump_63
        apply False.elim assump_46
      let assump_41 := assump_32 assump_62
      apply False.elim assump_41
    case inr assump_37 =>
      cases assump_37
      case intro assump_53 assump_54 =>
        apply False.elim assump_54
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_59
  apply False.elim assump_59


variable (p5 p3 p6 p0 p7 p4 : Prop)
theorem file46_916 : (((((False ∧ p3) ∨ (p0 ∨ p5)) → ((p5 → False) → (p6 → p6))) → False) → ((((p6 → False) ∧ (p5 → p4)) ∧ ((p4 → p3) → False)) ∨ (((p7 ∨ True) ∨ (p6 ∧ p6)) ∧ ((False → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  apply And.intro
  intro assump_4
  have assump_85 : (((False ∧ p3) ∨ (p0 ∨ p5)) → ((p5 → False) → (p6 → p6))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_9
    case inl assump_16 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
    case inr assump_17 =>
      cases assump_17
      case inl assump_22 =>
        exact assump_11
      case inr assump_23 =>
        exact assump_11
  let assump_8 := assump_1 assump_85
  apply False.elim assump_8
  intro assump_31
  have assump_86 : (((False ∧ p3) ∨ (p0 ∨ p5)) → ((p5 → False) → (p6 → p6))) := by
    intro assump_36
    intro assump_37
    intro assump_38
    cases assump_36
    case inl assump_43 =>
      cases assump_43
      case intro assump_45 assump_46 =>
        apply False.elim assump_45
    case inr assump_44 =>
      cases assump_44
      case inl assump_49 =>
        exact assump_38
      case inr assump_50 =>
        exact assump_38
  let assump_35 := assump_1 assump_86
  apply False.elim assump_35
  intro assump_58
  have assump_87 : (((False ∧ p3) ∨ (p0 ∨ p5)) → ((p5 → False) → (p6 → p6))) := by
    intro assump_63
    intro assump_64
    intro assump_65
    cases assump_63
    case inl assump_70 =>
      cases assump_70
      case intro assump_72 assump_73 =>
        apply False.elim assump_72
    case inr assump_71 =>
      cases assump_71
      case inl assump_76 =>
        exact assump_65
      case inr assump_77 =>
        exact assump_65
  let assump_62 := assump_1 assump_87
  apply False.elim assump_62


variable (p1 p7 p6 p0 p3 p4 p5 p2 : Prop)
theorem file46_2803 : (((((p6 ∨ p3) → False) → ((p7 ∧ p2) → (p2 ∨ p4))) ∨ (((True → p6) → False) ∧ ((p0 → p4) → (True → p0)))) ∨ ((((p6 → False) ∨ (p0 ∧ False)) ∨ ((p7 → False) ∧ (p5 → False))) ∨ (((p6 ∨ p5) → False) ∨ ((True ∧ p7) ∧ (p7 ∧ p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    apply Or.inl
    exact assump_8


variable (p2 p1 p0 p7 : Prop)
theorem file46_3240 : (((((p0 → p2) ∨ (p1 ∨ True)) → False) ∧ (((p0 ∨ True) → (False → False)) ∧ ((p2 → False) ∧ (p2 ∧ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          have assump_26 : p2 := by
            exact assump_14
          let assump_22 := assump_10 assump_26
          apply False.elim assump_22


variable (p0 p2 p1 p4 p6 p5 : Prop)
theorem file46_3817 : ((((((p0 ∧ False) ∧ (p0 ∧ p4)) → ((p1 → p6) ∨ (p1 ∧ p5))) ∨ (((p6 ∧ p5) → False) ∨ ((p2 → False) ∨ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p0 ∧ False) ∧ (p0 ∧ p4)) → ((p1 → p6) ∨ (p1 ∧ p5))) ∨ (((p6 ∧ p5) → False) ∨ ((p2 → False) ∨ (p2 → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p4 p3 : Prop)
theorem file46_4408 : (((((False ∧ p4) ∧ (p3 → p4)) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((False ∧ p4) ∧ (p3 → p4)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p0 p7 p3 p6 p1 p4 p5 : Prop)
theorem file46_4848 : (((((p5 ∨ True) → (p5 ∧ p0)) ∨ ((False → False) → (p2 ∨ p7))) → (((True ∨ p2) ∨ (p6 ∧ p3)) ∨ ((p6 ∨ p4) ∧ (p4 → p4)))) → ((((p7 ∧ p6) ∧ (p0 → False)) ∧ ((p2 ∨ p3) → (p1 ∨ p6))) ∨ (((p1 ∨ False) → (p3 ∨ p1)) → ((False → p0) → (False → p5))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  intro assump_5
  intro assump_6
  apply False.elim assump_6


variable (p7 p6 p5 p2 p1 p0 p4 : Prop)
theorem file46_5270 : (((((p1 → False) → (p5 ∨ p2)) ∧ ((False → False) ∧ (False ∧ True))) ∨ (((False → False) ∨ (p2 → p4)) ∧ ((p0 ∧ p5) → False))) → ((((p6 → p2) ∧ (False ∨ p6)) → ((False → False) ∨ (p2 ∧ p7))) ∨ (((False → p1) → (p7 ∨ p1)) → ((p0 → False) ∧ (p1 ∨ p7))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  case inr assump_3 =>
    cases assump_3
    case intro assump_16 assump_17 =>
      cases assump_16
      case inl assump_18 =>
        apply Or.inl
        intro assump_24
        cases assump_24
        case intro assump_25 assump_26 =>
          cases assump_26
          case inl assump_29 =>
            apply False.elim assump_29
          case inr assump_30 =>
            apply Or.inl
            intro assump_35
            apply False.elim assump_35
      case inr assump_19 =>
        apply Or.inl
        intro assump_42
        cases assump_42
        case intro assump_43 assump_44 =>
          cases assump_44
          case inl assump_47 =>
            apply False.elim assump_47
          case inr assump_48 =>
            apply Or.inl
            intro assump_53
            apply False.elim assump_53


variable (p0 p2 p5 p7 p1 p6 p3 p4 : Prop)
theorem file46_6688 : (((((True ∨ p5) → False) → ((True → True) → False)) ∧ (((False → p3) → False) ∧ ((p0 ∧ p6) → (True → p2)))) → ((((p4 ∧ True) → (p7 → p0)) → ((p4 ∨ p3) → False)) ∨ (((p1 ∧ p6) ∨ (True ∨ p2)) ∧ ((False → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      intro assump_13
      cases assump_13
      case inl assump_14 =>
        have assump_45 : (False → p3) := by
          intro assump_25
          apply False.elim assump_25
        let assump_24 := assump_6 assump_45
        apply False.elim assump_24
      case inr assump_15 =>
        have assump_46 : (False → p3) := by
          intro assump_39
          apply False.elim assump_39
        let assump_38 := assump_6 assump_46
        apply False.elim assump_38


variable (p7 p3 p5 p2 : Prop)
theorem file46_7605 : ((((((True ∨ p5) ∧ (p3 ∧ p2)) ∧ ((True → p5) ∨ (p5 ∨ False))) → (((p3 → False) → False) ∨ ((True → False) ∨ (True → p7)))) → False) → False) := by
  intro assump_1
  have assump_79 : ((((True ∨ p5) ∧ (p3 ∧ p2)) ∧ ((True → p5) ∨ (p5 ∨ False))) → (((p3 → False) → False) ∨ ((True → False) ∨ (True → p7)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            cases assump_7
            case inl assump_20 =>
              apply Or.inl
              intro assump_24
              have assump_80 : p3 := by
                exact assump_14
              let assump_27 := assump_24 assump_80
              apply False.elim assump_27
            case inr assump_21 =>
              cases assump_21
              case inl assump_31 =>
                apply Or.inl
                intro assump_35
                have assump_81 : p3 := by
                  exact assump_14
                let assump_38 := assump_35 assump_81
                apply False.elim assump_38
              case inr assump_32 =>
                apply False.elim assump_32
        case inr assump_11 =>
          cases assump_9
          case intro assump_46 assump_47 =>
            cases assump_7
            case inl assump_52 =>
              apply Or.inl
              intro assump_56
              have assump_82 : p3 := by
                exact assump_46
              let assump_59 := assump_56 assump_82
              apply False.elim assump_59
            case inr assump_53 =>
              cases assump_53
              case inl assump_63 =>
                apply Or.inl
                intro assump_67
                have assump_83 : p3 := by
                  exact assump_46
                let assump_70 := assump_67 assump_83
                apply False.elim assump_70
              case inr assump_64 =>
                apply False.elim assump_64
  let assump_4 := assump_1 assump_79
  apply False.elim assump_4


variable (p0 p3 p1 p7 p6 p2 p4 p5 : Prop)
theorem file46_9788 : (((((p0 → False) ∧ (True → False)) → ((p6 → False) ∧ (p5 → True))) ∧ (((False ∧ p3) → False) ∨ ((p6 ∨ p4) → (p5 → p5)))) ∧ ((((p0 ∧ False) → (p0 → p1)) ∧ ((p3 ∨ True) → False)) → (((p4 ∨ p7) ∧ (p3 → False)) ∧ ((p2 ∧ p6) ∧ (p2 → False))))) := by
  apply And.intro
  apply And.intro
  intro assump_19
  apply And.intro
  intro assump_20
  cases assump_19
  case intro assump_23 assump_24 =>
    have assump_96 : True := by
      apply True.intro
    let assump_29 := assump_24 assump_96
    apply False.elim assump_29
  intro assump_33
  apply True.intro
  apply Or.inl
  intro assump_34
  cases assump_34
  case intro assump_35 assump_36 =>
    apply False.elim assump_35
  intro assump_39
  apply And.intro
  apply And.intro
  cases assump_39
  case intro assump_40 assump_41 =>
    have assump_97 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_46 := assump_41 assump_97
    apply False.elim assump_46
  intro assump_50
  cases assump_39
  case intro assump_53 assump_54 =>
    have assump_98 : (p3 ∨ True) := by
      apply Or.inl
      exact assump_50
    let assump_59 := assump_54 assump_98
    apply False.elim assump_59
  apply And.intro
  apply And.intro
  cases assump_39
  case intro assump_63 assump_64 =>
    have assump_99 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_69 := assump_64 assump_99
    apply False.elim assump_69
  cases assump_39
  case intro assump_73 assump_74 =>
    have assump_100 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_79 := assump_74 assump_100
    apply False.elim assump_79
  intro assump_83
  cases assump_39
  case intro assump_86 assump_87 =>
    have assump_101 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_92 := assump_87 assump_101
    apply False.elim assump_92


variable (p3 p7 p5 p4 p0 p1 : Prop)
theorem file46_11683 : ((((((p5 → False) → False) → False) → (((True ∨ p3) ∨ (p1 ∧ False)) ∨ ((p0 → False) ∨ (p7 → p4)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 → False) → False) → False) → (((True ∨ p3) ∨ (p1 ∧ False)) ∨ ((p0 → False) ∨ (p7 → p4)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p1 p7 p4 p5 p2 : Prop)
theorem file46_12161 : (((((p2 ∧ p5) → (p4 → p2)) ∨ ((p1 → p7) ∧ (p2 → False))) ∧ (((p6 ∨ p1) ∨ (p6 → False)) → False)) → ((((p7 → False) → (p4 → p4)) → False) → False)) := by
  intro assump_42
  intro assump_43
  cases assump_42
  case intro assump_46 assump_47 =>
    cases assump_46
    case inl assump_48 =>
      have assump_86 : ((p6 ∨ p1) ∨ (p6 → False)) := by
        apply Or.inr
        intro assump_55
        have assump_87 : ((p6 ∨ p1) ∨ (p6 → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_55
        let assump_59 := assump_47 assump_87
        apply False.elim assump_59
      let assump_54 := assump_47 assump_86
      apply False.elim assump_54
    case inr assump_49 =>
      cases assump_49
      case intro assump_66 assump_67 =>
        have assump_88 : ((p6 ∨ p1) ∨ (p6 → False)) := by
          apply Or.inr
          intro assump_75
          have assump_89 : ((p6 ∨ p1) ∨ (p6 → False)) := by
            apply Or.inl
            apply Or.inl
            exact assump_75
          let assump_79 := assump_47 assump_89
          apply False.elim assump_79
        let assump_74 := assump_47 assump_88
        apply False.elim assump_74


variable (p5 p2 p7 : Prop)
theorem file46_13385 : (((((p7 ∧ p5) ∧ (p2 → False)) ∨ ((False ∧ True) → False)) → False) → False) := by
  intro assump_1
  have assump_13 : (((p7 ∧ p5) ∧ (p2 → False)) ∨ ((False ∧ True) → False)) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p6 p7 p1 p2 p0 p4 p3 : Prop)
theorem file46_13819 : ((((((p0 → p4) ∧ (p0 ∧ p4)) ∨ ((True ∨ p3) → (True ∨ p1))) ∧ (((p4 ∧ False) ∨ (p7 ∧ p2)) ∧ ((p4 ∧ p4) ∨ (False ∧ p5)))) ∧ ((((True → p7) → (p6 → p6)) → ((False ∧ True) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  apply False.elim assump_23
              case inr assump_21 =>
                cases assump_21
                case intro assump_28 assump_29 =>
                  cases assump_19
                  case inl assump_34 =>
                    cases assump_34
                    case intro assump_36 assump_37 =>
                      have assump_100 : (((True → p7) → (p6 → p6)) → ((False ∧ True) → False)) := by
                        intro assump_45
                        intro assump_46
                        cases assump_46
                        case intro assump_47 assump_48 =>
                          apply False.elim assump_47
                      let assump_44 := assump_3 assump_100
                      apply False.elim assump_44
                  case inr assump_35 =>
                    cases assump_35
                    case intro assump_54 assump_55 =>
                      apply False.elim assump_54
      case inr assump_7 =>
        cases assump_5
        case intro assump_60 assump_61 =>
          cases assump_60
          case inl assump_62 =>
            cases assump_62
            case intro assump_64 assump_65 =>
              apply False.elim assump_65
          case inr assump_63 =>
            cases assump_63
            case intro assump_70 assump_71 =>
              cases assump_61
              case inl assump_76 =>
                cases assump_76
                case intro assump_78 assump_79 =>
                  have assump_101 : (((True → p7) → (p6 → p6)) → ((False ∧ True) → False)) := by
                    intro assump_87
                    intro assump_88
                    cases assump_88
                    case intro assump_89 assump_90 =>
                      apply False.elim assump_89
                  let assump_86 := assump_3 assump_101
                  apply False.elim assump_86
              case inr assump_77 =>
                cases assump_77
                case intro assump_96 assump_97 =>
                  apply False.elim assump_96


variable (p3 p0 p4 p1 p6 p5 p2 : Prop)
theorem file46_16645 : (((((p1 → False) ∨ (p2 ∧ p6)) → ((p6 ∨ p3) ∧ (True ∨ p2))) → (((p3 → p6) → (p2 → False)) ∨ ((p0 → p2) ∨ (p3 ∧ p3)))) → ((((p5 ∧ p5) ∨ (False ∧ p3)) ∧ ((p0 → p4) → False)) → (((p5 → False) → (False → False)) ∨ ((p4 → True) ∨ (True → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply Or.inl
        intro assump_17
        intro assump_18
        apply False.elim assump_18
    case inr assump_6 =>
      cases assump_6
      case intro assump_21 assump_22 =>
        apply False.elim assump_21


variable (p2 p4 p3 p7 p0 p1 p6 p5 : Prop)
theorem file46_17373 : (((((p6 ∨ p2) → False) → ((p3 → True) ∨ (p4 → p1))) ∧ (((True ∧ p0) ∧ (p7 ∧ False)) → False)) ∨ ((((p2 → False) → False) ∨ ((p5 ∨ p0) → False)) → (((p4 → False) ∧ (p6 → False)) ∧ ((p3 ∨ p6) ∨ (True → False))))) := by
  apply Or.inl
  apply And.intro
  intro assump_7
  apply Or.inl
  intro assump_10
  apply True.intro
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_13
      case intro assump_20 assump_21 =>
        apply False.elim assump_21


variable (p6 p1 p5 p0 p2 p3 p4 p7 : Prop)
theorem file46_17985 : ((((((p6 → p0) → (p3 ∨ p7)) → False) ∨ (((p1 → False) ∧ (p4 ∧ p0)) → ((True ∧ False) → False))) ∧ ((((False → False) → (False → p4)) → False) ∧ (((p0 ∨ False) → (p2 → p6)) ∨ ((False → p2) ∨ (p5 → p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_92 : ((False → False) → (False → p4)) := by
            intro assump_18
            intro assump_19
            apply False.elim assump_19
          let assump_17 := assump_8 assump_92
          apply False.elim assump_17
        case inr assump_13 =>
          cases assump_13
          case inl assump_25 =>
            have assump_93 : ((False → False) → (False → p4)) := by
              intro assump_31
              intro assump_32
              apply False.elim assump_32
            let assump_30 := assump_8 assump_93
            apply False.elim assump_30
          case inr assump_26 =>
            have assump_94 : ((False → False) → (False → p4)) := by
              intro assump_42
              intro assump_43
              apply False.elim assump_43
            let assump_41 := assump_8 assump_94
            apply False.elim assump_41
    case inr assump_5 =>
      cases assump_3
      case intro assump_51 assump_52 =>
        cases assump_52
        case inl assump_55 =>
          have assump_95 : ((False → False) → (False → p4)) := by
            intro assump_61
            intro assump_62
            apply False.elim assump_62
          let assump_60 := assump_51 assump_95
          apply False.elim assump_60
        case inr assump_56 =>
          cases assump_56
          case inl assump_68 =>
            have assump_96 : ((False → False) → (False → p4)) := by
              intro assump_74
              intro assump_75
              apply False.elim assump_75
            let assump_73 := assump_51 assump_96
            apply False.elim assump_73
          case inr assump_69 =>
            have assump_97 : ((False → False) → (False → p4)) := by
              intro assump_85
              intro assump_86
              apply False.elim assump_86
            let assump_84 := assump_51 assump_97
            apply False.elim assump_84


variable (p1 p5 p4 p0 p2 p3 p6 : Prop)
theorem file46_20386 : ((((((p1 ∨ p5) ∧ (False ∧ p5)) ∨ ((p3 ∧ False) → False)) ∨ (((p4 ∨ p2) → False) ∧ ((p0 ∨ p6) → (p0 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p1 ∨ p5) ∧ (False ∧ p5)) ∨ ((p3 ∧ False) → False)) ∨ (((p4 ∨ p2) → False) ∧ ((p0 ∨ p6) → (p0 ∨ p4)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p3 p0 p4 p2 p7 p1 p5 : Prop)
theorem file46_20937 : (((((p2 ∨ p2) ∧ (False ∧ p1)) → False) ∨ (((p3 ∧ p3) ∨ (p6 ∨ p5)) ∨ ((p4 ∨ p1) → False))) ∨ ((((p6 → False) ∧ (p0 ∨ p4)) ∨ ((p2 ∨ p5) → False)) → (((p6 → p7) → (False → p7)) ∨ ((p6 → False) → (p1 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    case inr assump_5 =>
      cases assump_3
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p4 p5 p1 p6 p2 p7 p0 : Prop)
theorem file46_21571 : (((((False ∨ True) → False) → ((p5 ∧ p1) ∨ (p5 → False))) → False) → ((((p0 → p7) ∨ (True → False)) → ((p4 ∨ True) → False)) ∨ (((p2 ∨ p4) → (p1 ∨ p4)) ∧ ((p6 ∧ p0) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_4
    case inl assump_10 =>
      have assump_65 : (((False ∨ True) → False) → ((p5 ∧ p1) ∨ (p5 → False))) := by
        intro assump_17
        apply Or.inr
        intro assump_20
        have assump_66 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_24 := assump_17 assump_66
        apply False.elim assump_24
      let assump_16 := assump_1 assump_65
      apply False.elim assump_16
    case inr assump_11 =>
      have assump_67 : True := by
        apply True.intro
      let assump_33 := assump_11 assump_67
      apply False.elim assump_33
  case inr assump_7 =>
    cases assump_4
    case inl assump_39 =>
      have assump_68 : (((False ∨ True) → False) → ((p5 ∧ p1) ∨ (p5 → False))) := by
        intro assump_45
        apply Or.inr
        intro assump_48
        have assump_69 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_52 := assump_45 assump_69
        apply False.elim assump_52
      let assump_44 := assump_1 assump_68
      apply False.elim assump_44
    case inr assump_40 =>
      have assump_70 : True := by
        apply True.intro
      let assump_61 := assump_40 assump_70
      apply False.elim assump_61


variable (p3 p4 p0 p2 p5 p1 p6 : Prop)
theorem file46_23168 : ((((((p6 → False) ∧ (p0 → p2)) ∨ ((p1 ∨ False) → False)) ∨ (((p1 → False) ∧ (p5 ∧ p2)) ∧ ((p4 ∨ p6) ∨ (p4 ∨ p2)))) ∧ ((((p3 ∧ p1) ∨ (p1 → p3)) → False) ∧ (((p2 ∧ False) → (p6 → p4)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            have assump_162 : ((p2 ∧ False) → (p6 → p4)) := by
              intro assump_21
              intro assump_22
              cases assump_21
              case intro assump_25 assump_26 =>
                apply False.elim assump_26
            let assump_20 := assump_15 assump_162
            apply False.elim assump_20
      case inr assump_7 =>
        cases assump_3
        case intro assump_36 assump_37 =>
          have assump_163 : ((p2 ∧ False) → (p6 → p4)) := by
            intro assump_43
            intro assump_44
            cases assump_43
            case intro assump_47 assump_48 =>
              apply False.elim assump_48
          let assump_42 := assump_37 assump_163
          apply False.elim assump_42
    case inr assump_5 =>
      cases assump_5
      case intro assump_56 assump_57 =>
        cases assump_56
        case intro assump_58 assump_59 =>
          cases assump_59
          case intro assump_62 assump_63 =>
            cases assump_57
            case inl assump_68 =>
              cases assump_68
              case inl assump_70 =>
                cases assump_3
                case intro assump_74 assump_75 =>
                  have assump_164 : ((p2 ∧ False) → (p6 → p4)) := by
                    intro assump_81
                    intro assump_82
                    cases assump_81
                    case intro assump_85 assump_86 =>
                      apply False.elim assump_86
                  let assump_80 := assump_75 assump_164
                  apply False.elim assump_80
              case inr assump_71 =>
                cases assump_3
                case intro assump_96 assump_97 =>
                  have assump_165 : ((p2 ∧ False) → (p6 → p4)) := by
                    intro assump_103
                    intro assump_104
                    cases assump_103
                    case intro assump_107 assump_108 =>
                      apply False.elim assump_108
                  let assump_102 := assump_97 assump_165
                  apply False.elim assump_102
            case inr assump_69 =>
              cases assump_69
              case inl assump_116 =>
                cases assump_3
                case intro assump_120 assump_121 =>
                  have assump_166 : ((p2 ∧ False) → (p6 → p4)) := by
                    intro assump_127
                    intro assump_128
                    cases assump_127
                    case intro assump_131 assump_132 =>
                      apply False.elim assump_132
                  let assump_126 := assump_121 assump_166
                  apply False.elim assump_126
              case inr assump_117 =>
                cases assump_3
                case intro assump_142 assump_143 =>
                  have assump_167 : ((p2 ∧ False) → (p6 → p4)) := by
                    intro assump_149
                    intro assump_150
                    cases assump_149
                    case intro assump_153 assump_154 =>
                      apply False.elim assump_154
                  let assump_148 := assump_143 assump_167
                  apply False.elim assump_148


variable (p1 p3 p0 p4 p7 p5 p6 : Prop)
theorem file46_26875 : (((((False → False) ∧ (p0 ∧ p0)) → ((p3 → p5) → (p4 → p0))) ∨ (((p4 ∧ p1) ∨ (p3 → p5)) ∧ ((p5 → False) → False))) ∨ ((((p3 → p3) → (p7 ∨ p3)) ∧ ((p7 → False) ∧ (p1 ∨ p6))) ∧ (((p5 → p0) → (p0 ∧ p0)) ∧ ((p7 ∨ p5) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_4
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      exact assump_16


variable (p4 p0 p1 p6 p7 p2 p5 : Prop)
theorem file46_27382 : (((((p7 → p7) → False) ∧ ((p4 ∧ True) → False)) → (((p6 → p7) ∧ (p5 ∨ False)) ∧ ((p4 → p7) → False))) ∨ ((((p0 → p4) ∧ (True → False)) ∧ ((p2 ∧ p6) ∨ (p1 ∨ p6))) ∧ (((p4 → True) ∧ (p5 ∨ p2)) → ((p4 ∨ True) → (p7 ∨ False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_50 : (p7 → p7) := by
      intro assump_13
      exact assump_13
    let assump_12 := assump_5 assump_50
    apply False.elim assump_12
  cases assump_1
  case intro assump_19 assump_20 =>
    have assump_51 : (p7 → p7) := by
      intro assump_27
      exact assump_27
    let assump_26 := assump_19 assump_51
    apply False.elim assump_26
  intro assump_33
  cases assump_1
  case intro assump_36 assump_37 =>
    have assump_52 : (p7 → p7) := by
      intro assump_44
      exact assump_44
    let assump_43 := assump_36 assump_52
    apply False.elim assump_43


variable (p7 p3 p6 p5 : Prop)
theorem file46_28385 : ((((((p3 → False) ∨ (True → False)) → ((p6 ∧ p6) → (p3 → True))) ∨ (((p5 ∨ p6) → (p5 ∨ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p3 → False) ∨ (True → False)) → ((p6 ∧ p6) → (p3 → True))) ∨ (((p5 ∨ p6) → (p5 ∨ p7)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p7 p6 p2 p4 p1 : Prop)
theorem file46_28873 : ((((((p0 ∧ p2) ∧ (p4 → p6)) → False) → False) ∧ ((((p1 → True) → False) ∧ ((False → p0) ∨ (p2 → False))) ∨ (((p7 ∨ True) ∨ (p2 ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_36 : (p1 → True) := by
            intro assump_18
            apply True.intro
          let assump_17 := assump_8 assump_36
          apply False.elim assump_17
        case inr assump_13 =>
          have assump_37 : (p1 → True) := by
            intro assump_26
            apply True.intro
          let assump_25 := assump_8 assump_37
          apply False.elim assump_25
    case inr assump_7 =>
      have assump_38 : ((p7 ∨ True) ∨ (p2 ∨ p0)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_32 := assump_7 assump_38
      apply False.elim assump_32


variable (p7 p6 p2 p0 p5 p3 p1 : Prop)
theorem file46_29942 : (((((p1 → False) ∧ (False ∧ p7)) → ((p0 ∨ True) ∧ (p7 → False))) ∨ (((p6 → False) → (p0 ∧ False)) → ((p5 ∨ p6) ∧ (p1 → p0)))) ∨ ((((p5 ∨ p0) ∨ (p0 ∧ p1)) → ((True ∧ p2) → (False ∨ False))) ∨ (((p1 ∧ p3) ∨ (p5 → False)) → ((p7 ∨ p0) → (False ∨ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  intro assump_10
  cases assump_1
  case intro assump_13 assump_14 =>
    cases assump_14
    case intro assump_17 assump_18 =>
      apply False.elim assump_17


variable (p6 p7 p2 p0 p3 : Prop)
theorem file46_30621 : (((((True → False) ∨ (p0 ∨ p3)) → ((p2 ∧ False) → (p0 ∧ p6))) → False) → ((((p0 ∧ p2) ∧ (p7 ∧ p7)) ∧ ((p7 ∨ True) ∨ (p3 → False))) → (((True → False) ∨ (p3 → True)) → False))) := by
  intro assump_51
  intro assump_52
  intro assump_53
  cases assump_53
  case inl assump_54 =>
    cases assump_52
    case intro assump_58 assump_59 =>
      cases assump_58
      case intro assump_60 assump_61 =>
        cases assump_60
        case intro assump_62 assump_63 =>
          cases assump_61
          case intro assump_68 assump_69 =>
            cases assump_59
            case inl assump_74 =>
              cases assump_74
              case inl assump_76 =>
                have assump_232 : (((True → False) ∨ (p0 ∨ p3)) → ((p2 ∧ False) → (p0 ∧ p6))) := by
                  intro assump_83
                  intro assump_84
                  apply And.intro
                  cases assump_84
                  case intro assump_85 assump_86 =>
                    apply False.elim assump_86
                  cases assump_84
                  case intro assump_91 assump_92 =>
                    apply False.elim assump_92
                let assump_82 := assump_51 assump_232
                apply False.elim assump_82
              case inr assump_77 =>
                have assump_233 : (((True → False) ∨ (p0 ∨ p3)) → ((p2 ∧ False) → (p0 ∧ p6))) := by
                  intro assump_105
                  intro assump_106
                  apply And.intro
                  cases assump_106
                  case intro assump_107 assump_108 =>
                    apply False.elim assump_108
                  cases assump_106
                  case intro assump_113 assump_114 =>
                    apply False.elim assump_114
                let assump_104 := assump_51 assump_233
                apply False.elim assump_104
            case inr assump_75 =>
              have assump_234 : (((True → False) ∨ (p0 ∨ p3)) → ((p2 ∧ False) → (p0 ∧ p6))) := by
                intro assump_127
                intro assump_128
                apply And.intro
                cases assump_128
                case intro assump_129 assump_130 =>
                  apply False.elim assump_130
                cases assump_128
                case intro assump_135 assump_136 =>
                  apply False.elim assump_136
              let assump_126 := assump_51 assump_234
              apply False.elim assump_126
  case inr assump_55 =>
    cases assump_52
    case intro assump_146 assump_147 =>
      cases assump_146
      case intro assump_148 assump_149 =>
        cases assump_148
        case intro assump_150 assump_151 =>
          cases assump_149
          case intro assump_156 assump_157 =>
            cases assump_147
            case inl assump_162 =>
              cases assump_162
              case inl assump_164 =>
                have assump_235 : (((True → False) ∨ (p0 ∨ p3)) → ((p2 ∧ False) → (p0 ∧ p6))) := by
                  intro assump_171
                  intro assump_172
                  apply And.intro
                  cases assump_172
                  case intro assump_173 assump_174 =>
                    apply False.elim assump_174
                  cases assump_172
                  case intro assump_179 assump_180 =>
                    apply False.elim assump_180
                let assump_170 := assump_51 assump_235
                apply False.elim assump_170
              case inr assump_165 =>
                have assump_236 : (((True → False) ∨ (p0 ∨ p3)) → ((p2 ∧ False) → (p0 ∧ p6))) := by
                  intro assump_193
                  intro assump_194
                  apply And.intro
                  cases assump_194
                  case intro assump_195 assump_196 =>
                    apply False.elim assump_196
                  cases assump_194
                  case intro assump_201 assump_202 =>
                    apply False.elim assump_202
                let assump_192 := assump_51 assump_236
                apply False.elim assump_192
            case inr assump_163 =>
              have assump_237 : (((True → False) ∨ (p0 ∨ p3)) → ((p2 ∧ False) → (p0 ∧ p6))) := by
                intro assump_215
                intro assump_216
                apply And.intro
                cases assump_216
                case intro assump_217 assump_218 =>
                  apply False.elim assump_218
                cases assump_216
                case intro assump_223 assump_224 =>
                  apply False.elim assump_224
              let assump_214 := assump_51 assump_237
              apply False.elim assump_214


variable (p6 p5 p2 p7 : Prop)
theorem file46_35304 : ((((((p2 ∧ True) → (p5 → p5)) → False) → (((True ∨ p6) → (True ∧ p5)) ∨ ((p7 → p7) ∧ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_47 : ((((p2 ∧ True) → (p5 → p5)) → False) → (((True ∨ p6) → (True ∧ p5)) ∨ ((p7 → p7) ∧ (False → False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply And.intro
    apply True.intro
    cases assump_8
    case inl assump_9 =>
      have assump_48 : ((p2 ∧ True) → (p5 → p5)) := by
        intro assump_14
        intro assump_15
        cases assump_14
        case intro assump_18 assump_19 =>
          exact assump_15
      let assump_13 := assump_5 assump_48
      apply False.elim assump_13
    case inr assump_10 =>
      have assump_49 : ((p2 ∧ True) → (p5 → p5)) := by
        intro assump_31
        intro assump_32
        cases assump_31
        case intro assump_35 assump_36 =>
          exact assump_32
      let assump_30 := assump_5 assump_49
      apply False.elim assump_30
  let assump_4 := assump_1 assump_47
  apply False.elim assump_4


variable (p3 p0 p5 p6 p4 : Prop)
theorem file46_36404 : ((((((p5 ∨ p4) ∧ (p0 ∨ True)) ∧ ((False ∧ False) ∧ (p0 → True))) ∨ (((p6 ∧ p0) → (p0 ∨ p4)) ∨ ((p3 → p4) → (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p5 ∨ p4) ∧ (p0 ∨ True)) ∧ ((False ∧ False) ∧ (p0 → True))) ∨ (((p6 ∧ p0) → (p0 ∨ p4)) ∨ ((p3 → p4) → (p3 → False)))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      exact assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p4 p6 p7 p2 : Prop)
theorem file46_36984 : (((((p6 → p5) → False) ∨ ((False ∧ p5) → False)) → (((p2 → False) → False) ∨ ((p7 ∧ True) → False))) → ((((p4 ∧ False) → (p5 ∧ True)) ∨ ((p2 ∧ True) → False)) ∨ (((p5 → p6) → (p7 ∧ False)) ∨ ((p2 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6
  apply True.intro


variable (p0 p4 p7 p3 p2 p6 : Prop)
theorem file46_37449 : (((((p4 ∨ p4) → False) → ((True ∨ p7) ∨ (p2 ∧ False))) → False) → ((((p4 ∨ p4) ∧ (p4 ∧ p0)) ∨ ((p2 ∨ p0) ∨ (False → False))) ∨ (((p3 ∧ p6) ∧ (p2 → False)) → ((p6 → False) → (p6 ∧ p6))))) := by
  intro assump_5
  apply Or.inl
  apply Or.inr
  apply Or.inr
  intro assump_8
  apply False.elim assump_8


variable (p3 p6 p2 p7 p0 p4 : Prop)
theorem file46_37809 : (((((False ∧ p7) → False) ∨ ((p2 → p4) → False)) ∨ (((p0 ∧ p0) ∧ (p4 ∨ p3)) → False)) → ((((False ∧ p0) → (True → p0)) ∧ ((False ∨ p7) → (True ∨ p4))) ∨ (((p3 ∨ p2) → False) → ((False ∧ p4) → (False ∨ p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply And.intro
      intro assump_8
      intro assump_9
      cases assump_8
      case intro assump_12 assump_13 =>
        apply False.elim assump_12
      intro assump_16
      cases assump_16
      case inl assump_17 =>
        apply False.elim assump_17
      case inr assump_18 =>
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      apply Or.inl
      apply And.intro
      intro assump_25
      intro assump_26
      cases assump_25
      case intro assump_29 assump_30 =>
        apply False.elim assump_29
      intro assump_33
      cases assump_33
      case inl assump_34 =>
        apply False.elim assump_34
      case inr assump_35 =>
        apply Or.inl
        apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_42
    intro assump_43
    cases assump_42
    case intro assump_46 assump_47 =>
      apply False.elim assump_46
    intro assump_50
    cases assump_50
    case inl assump_51 =>
      apply False.elim assump_51
    case inr assump_52 =>
      apply Or.inl
      apply True.intro


variable (p1 p4 p0 p7 p5 p3 p2 : Prop)
theorem file46_39294 : ((((((p5 ∨ True) ∨ (p0 → False)) ∧ ((False ∧ p1) → False)) → (((p5 ∧ p3) → False) → ((p4 → False) ∧ (p5 ∧ p4)))) ∧ ((((p2 ∨ True) → (False → p3)) → ((p0 ∧ p0) → (p7 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p2 ∨ True) → (False → p3)) → ((p0 ∧ p0) → (p7 → True))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p6 p0 p4 p3 p1 p7 p5 : Prop)
theorem file46_39868 : (((((p5 → p1) ∨ (p7 ∨ p3)) ∨ ((p1 ∧ p5) → (p0 → p5))) → False) → ((((p3 ∨ p4) ∧ (True → False)) ∧ ((p3 → p7) ∧ (p5 → False))) ∨ (((p7 ∧ True) ∨ (p1 → False)) ∨ ((False ∨ p6) ∧ (True ∨ p0))))) := by
  intro assump_20
  apply Or.inr
  apply Or.inl
  apply Or.inr
  intro assump_23
  have assump_34 : (((p5 → p1) ∨ (p7 ∨ p3)) ∨ ((p1 ∧ p5) → (p0 → p5))) := by
    apply Or.inl
    apply Or.inl
    intro assump_28
    exact assump_23
  let assump_27 := assump_20 assump_34
  apply False.elim assump_27


variable (p4 p5 p1 p3 p7 p6 p0 : Prop)
theorem file46_40429 : ((((((p5 → False) ∧ (True → False)) ∨ ((p6 ∨ p3) → (p4 ∨ p4))) ∨ (((p0 → False) → False) → ((p4 ∨ p6) ∨ (p4 → p3)))) ∧ ((((p7 → False) ∧ (False ∧ p1)) → ((p7 → False) ∧ (False → p1))) ∧ (((False ∨ p3) → False) ∧ ((True ∧ p5) ∧ (p3 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_23
                  case intro assump_30 assump_31 =>
                    apply False.elim assump_31
      case inr assump_7 =>
        cases assump_3
        case intro assump_38 assump_39 =>
          cases assump_39
          case intro assump_42 assump_43 =>
            cases assump_43
            case intro assump_46 assump_47 =>
              cases assump_46
              case intro assump_48 assump_49 =>
                cases assump_47
                case intro assump_54 assump_55 =>
                  apply False.elim assump_55
    case inr assump_5 =>
      cases assump_3
      case intro assump_62 assump_63 =>
        cases assump_63
        case intro assump_66 assump_67 =>
          cases assump_67
          case intro assump_70 assump_71 =>
            cases assump_70
            case intro assump_72 assump_73 =>
              cases assump_71
              case intro assump_78 assump_79 =>
                apply False.elim assump_79


variable (p1 p3 p0 p2 p5 p7 p4 : Prop)
theorem file46_42268 : ((((((False → False) ∨ (p0 ∧ False)) ∨ ((p1 → p2) ∨ (p4 → p4))) ∧ (((p3 ∧ False) ∨ (True → False)) ∨ ((p1 → False) → (p5 → False)))) ∧ ((((True → False) → (p5 ∧ p4)) ∨ ((p4 ∨ True) → (p7 → False))) → False)) → False) := by
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
          case inl assump_12 =>
            cases assump_12
            case inl assump_14 =>
              cases assump_14
              case intro assump_16 assump_17 =>
                apply False.elim assump_17
            case inr assump_15 =>
              have assump_180 : (((True → False) → (p5 ∧ p4)) ∨ ((p4 ∨ True) → (p7 → False))) := by
                apply Or.inl
                intro assump_27
                apply And.intro
                have assump_181 : True := by
                  apply True.intro
                let assump_30 := assump_27 assump_181
                apply False.elim assump_30
                have assump_182 : True := by
                  apply True.intro
                let assump_36 := assump_27 assump_182
                apply False.elim assump_36
              let assump_26 := assump_3 assump_180
              apply False.elim assump_26
          case inr assump_13 =>
            have assump_183 : (((True → False) → (p5 ∧ p4)) ∨ ((p4 ∨ True) → (p7 → False))) := by
              apply Or.inl
              intro assump_48
              apply And.intro
              have assump_184 : True := by
                apply True.intro
              let assump_51 := assump_48 assump_184
              apply False.elim assump_51
              have assump_185 : True := by
                apply True.intro
              let assump_57 := assump_48 assump_185
              apply False.elim assump_57
            let assump_47 := assump_3 assump_183
            apply False.elim assump_47
        case inr assump_9 =>
          cases assump_9
          case intro assump_64 assump_65 =>
            apply False.elim assump_65
      case inr assump_7 =>
        cases assump_7
        case inl assump_70 =>
          cases assump_5
          case inl assump_74 =>
            cases assump_74
            case inl assump_76 =>
              cases assump_76
              case intro assump_78 assump_79 =>
                apply False.elim assump_79
            case inr assump_77 =>
              have assump_186 : (((True → False) → (p5 ∧ p4)) ∨ ((p4 ∨ True) → (p7 → False))) := by
                apply Or.inl
                intro assump_89
                apply And.intro
                have assump_187 : True := by
                  apply True.intro
                let assump_92 := assump_89 assump_187
                apply False.elim assump_92
                have assump_188 : True := by
                  apply True.intro
                let assump_98 := assump_89 assump_188
                apply False.elim assump_98
              let assump_88 := assump_3 assump_186
              apply False.elim assump_88
          case inr assump_75 =>
            have assump_189 : (((True → False) → (p5 ∧ p4)) ∨ ((p4 ∨ True) → (p7 → False))) := by
              apply Or.inl
              intro assump_110
              apply And.intro
              have assump_190 : True := by
                apply True.intro
              let assump_113 := assump_110 assump_190
              apply False.elim assump_113
              have assump_191 : True := by
                apply True.intro
              let assump_119 := assump_110 assump_191
              apply False.elim assump_119
            let assump_109 := assump_3 assump_189
            apply False.elim assump_109
        case inr assump_71 =>
          cases assump_5
          case inl assump_128 =>
            cases assump_128
            case inl assump_130 =>
              cases assump_130
              case intro assump_132 assump_133 =>
                apply False.elim assump_133
            case inr assump_131 =>
              have assump_192 : (((True → False) → (p5 ∧ p4)) ∨ ((p4 ∨ True) → (p7 → False))) := by
                apply Or.inl
                intro assump_143
                apply And.intro
                have assump_193 : True := by
                  apply True.intro
                let assump_146 := assump_143 assump_193
                apply False.elim assump_146
                have assump_194 : True := by
                  apply True.intro
                let assump_152 := assump_143 assump_194
                apply False.elim assump_152
              let assump_142 := assump_3 assump_192
              apply False.elim assump_142
          case inr assump_129 =>
            have assump_195 : (((True → False) → (p5 ∧ p4)) ∨ ((p4 ∨ True) → (p7 → False))) := by
              apply Or.inl
              intro assump_164
              apply And.intro
              have assump_196 : True := by
                apply True.intro
              let assump_167 := assump_164 assump_196
              apply False.elim assump_167
              have assump_197 : True := by
                apply True.intro
              let assump_173 := assump_164 assump_197
              apply False.elim assump_173
            let assump_163 := assump_3 assump_195
            apply False.elim assump_163


variable (p2 p5 p6 p4 p7 p3 p0 p1 : Prop)
theorem file46_47731 : (((((True → False) ∧ (p3 → False)) → ((True → p4) → False)) → (((False ∧ p6) ∨ (True ∧ p0)) → ((p1 ∨ p4) ∨ (p3 ∨ p0)))) ∨ ((((p4 → p6) → False) ∨ ((p6 → p2) → False)) ∨ (((p7 → p5) ∨ (False ∧ p3)) ∧ ((p1 → p3) ∨ (p1 ∧ p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5
  case inr assump_4 =>
    cases assump_4
    case intro assump_9 assump_10 =>
      apply Or.inr
      apply Or.inr
      exact assump_10


variable (p0 p5 p4 p3 p7 p2 : Prop)
theorem file46_48338 : ((((((p2 ∧ p0) ∧ (p5 ∧ p4)) → ((p3 ∨ True) ∨ (True ∨ p4))) ∨ (((p5 → p7) → False) ∨ ((p0 ∧ True) ∨ (p7 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p2 ∧ p0) ∧ (p5 ∧ p4)) → ((p3 ∨ True) ∨ (True ∨ p4))) ∨ (((p5 → p7) → False) ∨ ((p0 ∧ True) ∨ (p7 ∨ p4)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p1 p2 p6 p3 p7 p0 : Prop)
theorem file46_49042 : ((((((p3 → False) → (p7 ∨ False)) → False) → (((p0 → p0) ∨ (p0 → p0)) ∧ ((p5 → False) → False))) ∧ ((((p6 ∧ False) ∨ (p5 ∧ True)) ∨ ((p5 ∧ p1) → (p7 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_37 : (((p6 ∧ False) ∨ (p5 ∧ True)) ∨ ((p5 ∧ p1) → (p7 ∧ p2))) := by
      apply Or.inr
      intro assump_9
      apply And.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        have assump_38 : (((p6 ∧ False) ∨ (p5 ∧ True)) ∨ ((p5 ∧ p1) → (p7 ∧ p2))) := by
          apply Or.inl
          apply Or.inr
          apply And.intro
          exact assump_10
          apply True.intro
        let assump_18 := assump_3 assump_38
        apply False.elim assump_18
      cases assump_9
      case intro assump_22 assump_23 =>
        have assump_39 : (((p6 ∧ False) ∨ (p5 ∧ True)) ∨ ((p5 ∧ p1) → (p7 ∧ p2))) := by
          apply Or.inl
          apply Or.inr
          apply And.intro
          exact assump_22
          apply True.intro
        let assump_30 := assump_3 assump_39
        apply False.elim assump_30
    let assump_8 := assump_3 assump_37
    apply False.elim assump_8


variable (p7 p0 p6 p1 : Prop)
theorem file46_50267 : ((((((p6 → p7) → False) ∧ ((p1 → p6) ∧ (p0 ∧ p7))) → False) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p6 → p7) → False) ∧ ((p1 → p6) ∧ (p0 ∧ p7))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          have assump_34 : (p6 → p7) := by
            intro assump_24
            exact assump_15
          let assump_23 := assump_6 assump_34
          apply False.elim assump_23
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p3 p5 p4 p2 p0 p1 p7 p6 : Prop)
theorem file46_50965 : (((((p5 ∨ True) ∧ (False ∧ p7)) ∧ ((p7 → False) → (p4 → p5))) ∨ (((True → False) → False) ∨ ((p5 ∧ p6) ∨ (p1 ∨ False)))) → ((((p7 ∨ p2) ∧ (p0 ∧ p0)) ∧ ((p3 → False) ∨ (p0 ∧ p3))) → (((p6 ∨ p2) ∨ (p2 ∨ p3)) → ((p5 → p5) ∨ (False ∧ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              cases assump_11
              case inl assump_24 =>
                cases assump_1
                case inl assump_28 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case inl assump_34 =>
                        cases assump_33
                        case intro assump_38 assump_39 =>
                          apply False.elim assump_38
                      case inr assump_35 =>
                        cases assump_33
                        case intro assump_44 assump_45 =>
                          apply False.elim assump_44
                case inr assump_29 =>
                  cases assump_29
                  case inl assump_48 =>
                    apply Or.inl
                    intro assump_52
                    exact assump_52
                  case inr assump_49 =>
                    cases assump_49
                    case inl assump_55 =>
                      cases assump_55
                      case intro assump_57 assump_58 =>
                        apply Or.inl
                        intro assump_63
                        exact assump_63
                    case inr assump_56 =>
                      cases assump_56
                      case inl assump_66 =>
                        apply Or.inl
                        intro assump_70
                        exact assump_70
                      case inr assump_67 =>
                        apply False.elim assump_67
              case inr assump_25 =>
                cases assump_25
                case intro assump_75 assump_76 =>
                  cases assump_1
                  case inl assump_81 =>
                    cases assump_81
                    case intro assump_83 assump_84 =>
                      cases assump_83
                      case intro assump_85 assump_86 =>
                        cases assump_85
                        case inl assump_87 =>
                          cases assump_86
                          case intro assump_91 assump_92 =>
                            apply False.elim assump_91
                        case inr assump_88 =>
                          cases assump_86
                          case intro assump_97 assump_98 =>
                            apply False.elim assump_97
                  case inr assump_82 =>
                    cases assump_82
                    case inl assump_101 =>
                      apply Or.inl
                      intro assump_105
                      exact assump_105
                    case inr assump_102 =>
                      cases assump_102
                      case inl assump_108 =>
                        cases assump_108
                        case intro assump_110 assump_111 =>
                          apply Or.inl
                          intro assump_116
                          exact assump_116
                      case inr assump_109 =>
                        cases assump_109
                        case inl assump_119 =>
                          apply Or.inl
                          intro assump_123
                          exact assump_123
                        case inr assump_120 =>
                          apply False.elim assump_120
          case inr assump_15 =>
            cases assump_13
            case intro assump_130 assump_131 =>
              cases assump_11
              case inl assump_136 =>
                cases assump_1
                case inl assump_140 =>
                  cases assump_140
                  case intro assump_142 assump_143 =>
                    cases assump_142
                    case intro assump_144 assump_145 =>
                      cases assump_144
                      case inl assump_146 =>
                        cases assump_145
                        case intro assump_150 assump_151 =>
                          apply False.elim assump_150
                      case inr assump_147 =>
                        cases assump_145
                        case intro assump_156 assump_157 =>
                          apply False.elim assump_156
                case inr assump_141 =>
                  cases assump_141
                  case inl assump_160 =>
                    apply Or.inl
                    intro assump_164
                    exact assump_164
                  case inr assump_161 =>
                    cases assump_161
                    case inl assump_167 =>
                      cases assump_167
                      case intro assump_169 assump_170 =>
                        apply Or.inl
                        intro assump_175
                        exact assump_175
                    case inr assump_168 =>
                      cases assump_168
                      case inl assump_178 =>
                        apply Or.inl
                        intro assump_182
                        exact assump_182
                      case inr assump_179 =>
                        apply False.elim assump_179
              case inr assump_137 =>
                cases assump_137
                case intro assump_187 assump_188 =>
                  cases assump_1
                  case inl assump_193 =>
                    cases assump_193
                    case intro assump_195 assump_196 =>
                      cases assump_195
                      case intro assump_197 assump_198 =>
                        cases assump_197
                        case inl assump_199 =>
                          cases assump_198
                          case intro assump_203 assump_204 =>
                            apply False.elim assump_203
                        case inr assump_200 =>
                          cases assump_198
                          case intro assump_209 assump_210 =>
                            apply False.elim assump_209
                  case inr assump_194 =>
                    cases assump_194
                    case inl assump_213 =>
                      apply Or.inl
                      intro assump_217
                      exact assump_217
                    case inr assump_214 =>
                      cases assump_214
                      case inl assump_220 =>
                        cases assump_220
                        case intro assump_222 assump_223 =>
                          apply Or.inl
                          intro assump_228
                          exact assump_228
                      case inr assump_221 =>
                        cases assump_221
                        case inl assump_231 =>
                          apply Or.inl
                          intro assump_235
                          exact assump_235
                        case inr assump_232 =>
                          apply False.elim assump_232
    case inr assump_7 =>
      cases assump_2
      case intro assump_242 assump_243 =>
        cases assump_242
        case intro assump_244 assump_245 =>
          cases assump_244
          case inl assump_246 =>
            cases assump_245
            case intro assump_250 assump_251 =>
              cases assump_243
              case inl assump_256 =>
                cases assump_1
                case inl assump_260 =>
                  cases assump_260
                  case intro assump_262 assump_263 =>
                    cases assump_262
                    case intro assump_264 assump_265 =>
                      cases assump_264
                      case inl assump_266 =>
                        cases assump_265
                        case intro assump_270 assump_271 =>
                          apply False.elim assump_270
                      case inr assump_267 =>
                        cases assump_265
                        case intro assump_276 assump_277 =>
                          apply False.elim assump_276
                case inr assump_261 =>
                  cases assump_261
                  case inl assump_280 =>
                    apply Or.inl
                    intro assump_284
                    exact assump_284
                  case inr assump_281 =>
                    cases assump_281
                    case inl assump_287 =>
                      cases assump_287
                      case intro assump_289 assump_290 =>
                        apply Or.inl
                        intro assump_295
                        exact assump_295
                    case inr assump_288 =>
                      cases assump_288
                      case inl assump_298 =>
                        apply Or.inl
                        intro assump_302
                        exact assump_302
                      case inr assump_299 =>
                        apply False.elim assump_299
              case inr assump_257 =>
                cases assump_257
                case intro assump_307 assump_308 =>
                  cases assump_1
                  case inl assump_313 =>
                    cases assump_313
                    case intro assump_315 assump_316 =>
                      cases assump_315
                      case intro assump_317 assump_318 =>
                        cases assump_317
                        case inl assump_319 =>
                          cases assump_318
                          case intro assump_323 assump_324 =>
                            apply False.elim assump_323
                        case inr assump_320 =>
                          cases assump_318
                          case intro assump_329 assump_330 =>
                            apply False.elim assump_329
                  case inr assump_314 =>
                    cases assump_314
                    case inl assump_333 =>
                      apply Or.inl
                      intro assump_337
                      exact assump_337
                    case inr assump_334 =>
                      cases assump_334
                      case inl assump_340 =>
                        cases assump_340
                        case intro assump_342 assump_343 =>
                          apply Or.inl
                          intro assump_348
                          exact assump_348
                      case inr assump_341 =>
                        cases assump_341
                        case inl assump_351 =>
                          apply Or.inl
                          intro assump_355
                          exact assump_355
                        case inr assump_352 =>
                          apply False.elim assump_352
          case inr assump_247 =>
            cases assump_245
            case intro assump_362 assump_363 =>
              cases assump_243
              case inl assump_368 =>
                cases assump_1
                case inl assump_372 =>
                  cases assump_372
                  case intro assump_374 assump_375 =>
                    cases assump_374
                    case intro assump_376 assump_377 =>
                      cases assump_376
                      case inl assump_378 =>
                        cases assump_377
                        case intro assump_382 assump_383 =>
                          apply False.elim assump_382
                      case inr assump_379 =>
                        cases assump_377
                        case intro assump_388 assump_389 =>
                          apply False.elim assump_388
                case inr assump_373 =>
                  cases assump_373
                  case inl assump_392 =>
                    apply Or.inl
                    intro assump_396
                    exact assump_396
                  case inr assump_393 =>
                    cases assump_393
                    case inl assump_399 =>
                      cases assump_399
                      case intro assump_401 assump_402 =>
                        apply Or.inl
                        intro assump_407
                        exact assump_407
                    case inr assump_400 =>
                      cases assump_400
                      case inl assump_410 =>
                        apply Or.inl
                        intro assump_414
                        exact assump_414
                      case inr assump_411 =>
                        apply False.elim assump_411
              case inr assump_369 =>
                cases assump_369
                case intro assump_419 assump_420 =>
                  cases assump_1
                  case inl assump_425 =>
                    cases assump_425
                    case intro assump_427 assump_428 =>
                      cases assump_427
                      case intro assump_429 assump_430 =>
                        cases assump_429
                        case inl assump_431 =>
                          cases assump_430
                          case intro assump_435 assump_436 =>
                            apply False.elim assump_435
                        case inr assump_432 =>
                          cases assump_430
                          case intro assump_441 assump_442 =>
                            apply False.elim assump_441
                  case inr assump_426 =>
                    cases assump_426
                    case inl assump_445 =>
                      apply Or.inl
                      intro assump_449
                      exact assump_449
                    case inr assump_446 =>
                      cases assump_446
                      case inl assump_452 =>
                        cases assump_452
                        case intro assump_454 assump_455 =>
                          apply Or.inl
                          intro assump_460
                          exact assump_460
                      case inr assump_453 =>
                        cases assump_453
                        case inl assump_463 =>
                          apply Or.inl
                          intro assump_467
                          exact assump_467
                        case inr assump_464 =>
                          apply False.elim assump_464
  case inr assump_5 =>
    cases assump_5
    case inl assump_472 =>
      cases assump_2
      case intro assump_476 assump_477 =>
        cases assump_476
        case intro assump_478 assump_479 =>
          cases assump_478
          case inl assump_480 =>
            cases assump_479
            case intro assump_484 assump_485 =>
              cases assump_477
              case inl assump_490 =>
                cases assump_1
                case inl assump_494 =>
                  cases assump_494
                  case intro assump_496 assump_497 =>
                    cases assump_496
                    case intro assump_498 assump_499 =>
                      cases assump_498
                      case inl assump_500 =>
                        cases assump_499
                        case intro assump_504 assump_505 =>
                          apply False.elim assump_504
                      case inr assump_501 =>
                        cases assump_499
                        case intro assump_510 assump_511 =>
                          apply False.elim assump_510
                case inr assump_495 =>
                  cases assump_495
                  case inl assump_514 =>
                    apply Or.inl
                    intro assump_518
                    exact assump_518
                  case inr assump_515 =>
                    cases assump_515
                    case inl assump_521 =>
                      cases assump_521
                      case intro assump_523 assump_524 =>
                        apply Or.inl
                        intro assump_529
                        exact assump_529
                    case inr assump_522 =>
                      cases assump_522
                      case inl assump_532 =>
                        apply Or.inl
                        intro assump_536
                        exact assump_536
                      case inr assump_533 =>
                        apply False.elim assump_533
              case inr assump_491 =>
                cases assump_491
                case intro assump_541 assump_542 =>
                  cases assump_1
                  case inl assump_547 =>
                    cases assump_547
                    case intro assump_549 assump_550 =>
                      cases assump_549
                      case intro assump_551 assump_552 =>
                        cases assump_551
                        case inl assump_553 =>
                          cases assump_552
                          case intro assump_557 assump_558 =>
                            apply False.elim assump_557
                        case inr assump_554 =>
                          cases assump_552
                          case intro assump_563 assump_564 =>
                            apply False.elim assump_563
                  case inr assump_548 =>
                    cases assump_548
                    case inl assump_567 =>
                      apply Or.inl
                      intro assump_571
                      exact assump_571
                    case inr assump_568 =>
                      cases assump_568
                      case inl assump_574 =>
                        cases assump_574
                        case intro assump_576 assump_577 =>
                          apply Or.inl
                          intro assump_582
                          exact assump_582
                      case inr assump_575 =>
                        cases assump_575
                        case inl assump_585 =>
                          apply Or.inl
                          intro assump_589
                          exact assump_589
                        case inr assump_586 =>
                          apply False.elim assump_586
          case inr assump_481 =>
            cases assump_479
            case intro assump_596 assump_597 =>
              cases assump_477
              case inl assump_602 =>
                cases assump_1
                case inl assump_606 =>
                  cases assump_606
                  case intro assump_608 assump_609 =>
                    cases assump_608
                    case intro assump_610 assump_611 =>
                      cases assump_610
                      case inl assump_612 =>
                        cases assump_611
                        case intro assump_616 assump_617 =>
                          apply False.elim assump_616
                      case inr assump_613 =>
                        cases assump_611
                        case intro assump_622 assump_623 =>
                          apply False.elim assump_622
                case inr assump_607 =>
                  cases assump_607
                  case inl assump_626 =>
                    apply Or.inl
                    intro assump_630
                    exact assump_630
                  case inr assump_627 =>
                    cases assump_627
                    case inl assump_633 =>
                      cases assump_633
                      case intro assump_635 assump_636 =>
                        apply Or.inl
                        intro assump_641
                        exact assump_641
                    case inr assump_634 =>
                      cases assump_634
                      case inl assump_644 =>
                        apply Or.inl
                        intro assump_648
                        exact assump_648
                      case inr assump_645 =>
                        apply False.elim assump_645
              case inr assump_603 =>
                cases assump_603
                case intro assump_653 assump_654 =>
                  cases assump_1
                  case inl assump_659 =>
                    cases assump_659
                    case intro assump_661 assump_662 =>
                      cases assump_661
                      case intro assump_663 assump_664 =>
                        cases assump_663
                        case inl assump_665 =>
                          cases assump_664
                          case intro assump_669 assump_670 =>
                            apply False.elim assump_669
                        case inr assump_666 =>
                          cases assump_664
                          case intro assump_675 assump_676 =>
                            apply False.elim assump_675
                  case inr assump_660 =>
                    cases assump_660
                    case inl assump_679 =>
                      apply Or.inl
                      intro assump_683
                      exact assump_683
                    case inr assump_680 =>
                      cases assump_680
                      case inl assump_686 =>
                        cases assump_686
                        case intro assump_688 assump_689 =>
                          apply Or.inl
                          intro assump_694
                          exact assump_694
                      case inr assump_687 =>
                        cases assump_687
                        case inl assump_697 =>
                          apply Or.inl
                          intro assump_701
                          exact assump_701
                        case inr assump_698 =>
                          apply False.elim assump_698
    case inr assump_473 =>
      cases assump_2
      case intro assump_708 assump_709 =>
        cases assump_708
        case intro assump_710 assump_711 =>
          cases assump_710
          case inl assump_712 =>
            cases assump_711
            case intro assump_716 assump_717 =>
              cases assump_709
              case inl assump_722 =>
                cases assump_1
                case inl assump_726 =>
                  cases assump_726
                  case intro assump_728 assump_729 =>
                    cases assump_728
                    case intro assump_730 assump_731 =>
                      cases assump_730
                      case inl assump_732 =>
                        cases assump_731
                        case intro assump_736 assump_737 =>
                          apply False.elim assump_736
                      case inr assump_733 =>
                        cases assump_731
                        case intro assump_742 assump_743 =>
                          apply False.elim assump_742
                case inr assump_727 =>
                  cases assump_727
                  case inl assump_746 =>
                    apply Or.inl
                    intro assump_750
                    exact assump_750
                  case inr assump_747 =>
                    cases assump_747
                    case inl assump_753 =>
                      cases assump_753
                      case intro assump_755 assump_756 =>
                        apply Or.inl
                        intro assump_761
                        exact assump_761
                    case inr assump_754 =>
                      cases assump_754
                      case inl assump_764 =>
                        apply Or.inl
                        intro assump_768
                        exact assump_768
                      case inr assump_765 =>
                        apply False.elim assump_765
              case inr assump_723 =>
                cases assump_723
                case intro assump_773 assump_774 =>
                  cases assump_1
                  case inl assump_779 =>
                    cases assump_779
                    case intro assump_781 assump_782 =>
                      cases assump_781
                      case intro assump_783 assump_784 =>
                        cases assump_783
                        case inl assump_785 =>
                          cases assump_784
                          case intro assump_789 assump_790 =>
                            apply False.elim assump_789
                        case inr assump_786 =>
                          cases assump_784
                          case intro assump_795 assump_796 =>
                            apply False.elim assump_795
                  case inr assump_780 =>
                    cases assump_780
                    case inl assump_799 =>
                      apply Or.inl
                      intro assump_803
                      exact assump_803
                    case inr assump_800 =>
                      cases assump_800
                      case inl assump_806 =>
                        cases assump_806
                        case intro assump_808 assump_809 =>
                          apply Or.inl
                          intro assump_814
                          exact assump_814
                      case inr assump_807 =>
                        cases assump_807
                        case inl assump_817 =>
                          apply Or.inl
                          intro assump_821
                          exact assump_821
                        case inr assump_818 =>
                          apply False.elim assump_818
          case inr assump_713 =>
            cases assump_711
            case intro assump_828 assump_829 =>
              cases assump_709
              case inl assump_834 =>
                cases assump_1
                case inl assump_838 =>
                  cases assump_838
                  case intro assump_840 assump_841 =>
                    cases assump_840
                    case intro assump_842 assump_843 =>
                      cases assump_842
                      case inl assump_844 =>
                        cases assump_843
                        case intro assump_848 assump_849 =>
                          apply False.elim assump_848
                      case inr assump_845 =>
                        cases assump_843
                        case intro assump_854 assump_855 =>
                          apply False.elim assump_854
                case inr assump_839 =>
                  cases assump_839
                  case inl assump_858 =>
                    apply Or.inl
                    intro assump_862
                    exact assump_862
                  case inr assump_859 =>
                    cases assump_859
                    case inl assump_865 =>
                      cases assump_865
                      case intro assump_867 assump_868 =>
                        apply Or.inl
                        intro assump_873
                        exact assump_873
                    case inr assump_866 =>
                      cases assump_866
                      case inl assump_876 =>
                        apply Or.inl
                        intro assump_880
                        exact assump_880
                      case inr assump_877 =>
                        apply False.elim assump_877
              case inr assump_835 =>
                cases assump_835
                case intro assump_885 assump_886 =>
                  cases assump_1
                  case inl assump_891 =>
                    cases assump_891
                    case intro assump_893 assump_894 =>
                      cases assump_893
                      case intro assump_895 assump_896 =>
                        cases assump_895
                        case inl assump_897 =>
                          cases assump_896
                          case intro assump_901 assump_902 =>
                            apply False.elim assump_901
                        case inr assump_898 =>
                          cases assump_896
                          case intro assump_907 assump_908 =>
                            apply False.elim assump_907
                  case inr assump_892 =>
                    cases assump_892
                    case inl assump_911 =>
                      apply Or.inl
                      intro assump_915
                      exact assump_915
                    case inr assump_912 =>
                      cases assump_912
                      case inl assump_918 =>
                        cases assump_918
                        case intro assump_920 assump_921 =>
                          apply Or.inl
                          intro assump_926
                          exact assump_926
                      case inr assump_919 =>
                        cases assump_919
                        case inl assump_929 =>
                          apply Or.inl
                          intro assump_933
                          exact assump_933
                        case inr assump_930 =>
                          apply False.elim assump_930


variable (p3 p1 p4 p5 p0 p7 : Prop)
theorem file46_80564 : (((((True ∧ False) ∧ (p3 ∧ p3)) → False) → False) → ((((p1 ∨ p0) → (p7 ∧ p4)) ∧ ((False → False) → (p3 → True))) ∧ (((p7 → p5) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    have assump_95 : (((True ∧ False) ∧ (p3 ∧ p3)) → False) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
    let assump_9 := assump_1 assump_95
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_96 : (((True ∧ False) ∧ (p3 ∧ p3)) → False) := by
      intro assump_27
      cases assump_27
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          apply False.elim assump_31
    let assump_26 := assump_1 assump_96
    apply False.elim assump_26
  cases assump_2
  case inl assump_39 =>
    have assump_97 : (((True ∧ False) ∧ (p3 ∧ p3)) → False) := by
      intro assump_46
      cases assump_46
      case intro assump_47 assump_48 =>
        cases assump_47
        case intro assump_49 assump_50 =>
          apply False.elim assump_50
    let assump_45 := assump_1 assump_97
    apply False.elim assump_45
  case inr assump_40 =>
    have assump_98 : (((True ∧ False) ∧ (p3 ∧ p3)) → False) := by
      intro assump_63
      cases assump_63
      case intro assump_64 assump_65 =>
        cases assump_64
        case intro assump_66 assump_67 =>
          apply False.elim assump_67
    let assump_62 := assump_1 assump_98
    apply False.elim assump_62
  intro assump_75
  intro assump_76
  apply True.intro
  intro assump_77
  have assump_99 : (((True ∧ False) ∧ (p3 ∧ p3)) → False) := by
    intro assump_83
    cases assump_83
    case intro assump_84 assump_85 =>
      cases assump_84
      case intro assump_86 assump_87 =>
        apply False.elim assump_87
  let assump_82 := assump_1 assump_99
  apply False.elim assump_82


variable (p1 p2 p4 : Prop)
theorem file46_82657 : (((((p2 ∧ p2) → (p1 ∧ p4)) → ((True → False) → (p2 → False))) → False) → False) := by
  intro assump_1
  have assump_25 : (((p2 ∧ p2) → (p1 ∧ p4)) → ((True → False) → (p2 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_26 : True := by
      apply True.intro
    let assump_18 := assump_6 assump_26
    apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p3 p4 p6 p2 p7 p1 p5 : Prop)
theorem file46_83156 : (((((p3 ∨ p5) → False) ∧ ((p7 → True) → False)) → (((p6 → False) → False) ∨ ((p1 → p2) → (p4 → p6)))) ∨ ((((p4 ∧ True) ∨ (p3 ∨ p1)) → ((p4 → False) ∧ (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inl
    intro assump_12
    have assump_21 : (p7 → True) := by
      intro assump_17
      apply True.intro
    let assump_16 := assump_7 assump_21
    apply False.elim assump_16


variable (p5 p2 p4 p7 : Prop)
theorem file46_83666 : (((((p4 → p4) → False) → ((False ∨ p4) ∨ (p7 ∧ p5))) → (((p4 ∨ p2) → (True ∨ False)) → ((p2 → p2) → False))) → False) := by
  intro assump_1
  have assump_30 : (((p4 → p4) → False) → ((False ∨ p4) ∨ (p7 ∧ p5))) := by
    intro assump_5
    have assump_31 : (p4 → p4) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_31
    apply False.elim assump_8
  let assump_4 := assump_1 assump_30
  have assump_32 : ((p4 ∨ p2) → (True ∨ False)) := by
    intro assump_16
    cases assump_16
    case inl assump_17 =>
      apply Or.inl
      apply True.intro
    case inr assump_18 =>
      apply Or.inl
      apply True.intro
  let assump_15 := assump_4 assump_32
  have assump_33 : (p2 → p2) := by
    intro assump_24
    exact assump_24
  let assump_23 := assump_15 assump_33
  apply False.elim assump_23


variable (p1 p7 p3 p2 p0 p5 p6 : Prop)
theorem file46_84561 : (((((p5 → p3) ∧ (True → False)) → False) → (((p1 ∧ False) → (False ∨ p6)) ∨ ((p3 ∨ p2) ∧ (p7 ∧ True)))) ∨ ((((False ∨ False) ∧ (p1 → False)) ∧ ((False → False) ∨ (p0 ∧ p2))) ∧ (((True → False) ∧ (p2 → False)) ∧ ((p0 → False) → (p2 → p0))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p0 p1 p7 p3 p6 p2 : Prop)
theorem file46_85013 : (((((p1 → p7) ∧ (True → p6)) ∧ ((p7 → False) ∧ (p0 ∨ p1))) ∧ (((p3 ∧ False) → (True → p3)) → False)) → ((((p3 ∧ True) → (p3 → False)) → False) ∧ (((p2 ∨ p7) → (p2 ∨ p2)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          cases assump_16
          case inl assump_19 =>
            have assump_112 : ((p3 ∧ False) → (True → p3)) := by
              intro assump_26
              intro assump_27
              cases assump_26
              case intro assump_30 assump_31 =>
                apply False.elim assump_31
            let assump_25 := assump_6 assump_112
            apply False.elim assump_25
          case inr assump_20 =>
            have assump_113 : ((p3 ∧ False) → (True → p3)) := by
              intro assump_44
              intro assump_45
              cases assump_44
              case intro assump_48 assump_49 =>
                apply False.elim assump_49
            let assump_43 := assump_6 assump_113
            apply False.elim assump_43
  intro assump_57
  cases assump_1
  case intro assump_60 assump_61 =>
    cases assump_60
    case intro assump_62 assump_63 =>
      cases assump_62
      case intro assump_64 assump_65 =>
        cases assump_63
        case intro assump_70 assump_71 =>
          cases assump_71
          case inl assump_74 =>
            have assump_114 : ((p3 ∧ False) → (True → p3)) := by
              intro assump_81
              intro assump_82
              cases assump_81
              case intro assump_85 assump_86 =>
                apply False.elim assump_86
            let assump_80 := assump_61 assump_114
            apply False.elim assump_80
          case inr assump_75 =>
            have assump_115 : ((p3 ∧ False) → (True → p3)) := by
              intro assump_99
              intro assump_100
              cases assump_99
              case intro assump_103 assump_104 =>
                apply False.elim assump_104
            let assump_98 := assump_61 assump_115
            apply False.elim assump_98


variable (p5 p0 p3 p1 p6 p2 p7 p4 : Prop)
theorem file46_87328 : (((((p2 ∨ True) → (p7 → False)) ∨ ((p1 → False) ∧ (p4 → p6))) → (((p6 → p1) ∧ (True → False)) → False)) ∨ ((((p7 → False) → (p6 ∧ p0)) → ((p2 ∧ p7) ∧ (p3 ∨ p7))) → (((p6 → True) → (p5 → p2)) ∨ ((p6 ∧ p4) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      have assump_31 : True := by
        apply True.intro
      let assump_15 := assump_4 assump_31
      apply False.elim assump_15
    case inr assump_10 =>
      cases assump_10
      case intro assump_19 assump_20 =>
        have assump_32 : True := by
          apply True.intro
        let assump_27 := assump_4 assump_32
        apply False.elim assump_27


variable (p1 p4 p7 p0 p6 p5 p2 : Prop)
theorem file46_88121 : (((((True ∨ p5) ∨ (False → True)) → False) → False) ∧ ((((False ∧ p7) → False) → ((True ∨ p1) → (p5 → True))) ∨ (((p0 ∨ p6) ∨ (p4 → False)) ∨ ((p2 → False) → False)))) := by
  apply And.intro
  intro assump_1
  have assump_11 : ((True ∨ p5) ∨ (False → True)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4
  apply Or.inl
  intro assump_8
  intro assump_9
  intro assump_10
  apply True.intro


variable (p3 p7 p6 p2 p1 p0 p5 p4 : Prop)
theorem file46_88658 : (((((p1 ∧ p4) ∨ (p3 → False)) ∨ ((p2 → False) ∧ (p7 → False))) → (((p0 → p0) → False) → False)) ∨ ((((p4 ∧ p5) ∧ (p1 ∨ p5)) ∧ ((p6 → False) → (p2 → p4))) → (((p6 → False) → (p7 ∨ p3)) → ((p4 → False) → False)))) := by
  apply Or.inl
  intro assump_7
  intro assump_8
  cases assump_7
  case inl assump_11 =>
    cases assump_11
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        have assump_55 : (p0 → p0) := by
          intro assump_24
          exact assump_24
        let assump_23 := assump_8 assump_55
        apply False.elim assump_23
    case inr assump_14 =>
      have assump_56 : (p0 → p0) := by
        intro assump_34
        exact assump_34
      let assump_33 := assump_8 assump_56
      apply False.elim assump_33
  case inr assump_12 =>
    cases assump_12
    case intro assump_40 assump_41 =>
      have assump_57 : (p0 → p0) := by
        intro assump_49
        exact assump_49
      let assump_48 := assump_8 assump_57
      apply False.elim assump_48


variable (p4 p6 p2 p7 p0 p1 : Prop)
theorem file46_89738 : ((((((True ∨ p7) ∨ (p4 → False)) ∨ ((p7 → False) ∧ (p4 → False))) ∨ (((True ∧ p2) → (p1 → p6)) → ((p0 ∧ p6) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ p7) ∨ (p4 → False)) ∨ ((p7 → False) ∧ (p4 → False))) ∨ (((True ∧ p2) → (p1 → p6)) → ((p0 ∧ p6) → (False → False)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p5 p4 p6 p2 p7 p0 p1 : Prop)
theorem file46_90278 : (((((p1 → False) → (p5 ∧ p5)) → ((p5 ∨ p7) ∨ (p6 ∧ p0))) → False) → ((((p2 ∧ p4) → False) ∨ ((True ∧ p1) → (p5 ∨ p2))) → (((p6 ∧ p1) → (False → p2)) ∨ ((p1 ∧ p3) ∧ (p3 ∧ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  case inr assump_4 =>
    apply Or.inl
    intro assump_17
    intro assump_18
    apply False.elim assump_18


variable (p6 p1 p0 p2 p4 : Prop)
theorem file46_90794 : (((((True → False) → (p0 → False)) → False) ∧ (((p1 ∧ True) → False) ∧ ((p2 ∧ p4) ∨ (p6 → p0)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_53 : ((True → False) → (p0 → False)) := by
            intro assump_22
            intro assump_23
            have assump_54 : True := by
              apply True.intro
            let assump_28 := assump_22 assump_54
            apply False.elim assump_28
          let assump_21 := assump_2 assump_53
          apply False.elim assump_21
      case inr assump_11 =>
        have assump_55 : ((True → False) → (p0 → False)) := by
          intro assump_40
          intro assump_41
          have assump_56 : True := by
            apply True.intro
          let assump_46 := assump_40 assump_56
          apply False.elim assump_46
        let assump_39 := assump_2 assump_55
        apply False.elim assump_39


variable (p5 p7 p6 p1 : Prop)
theorem file46_91934 : ((((((p7 → p6) → False) → False) → (((True → p5) → False) → ((False ∧ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p7 → p6) → False) → False) → (((True → p5) → False) → ((False ∧ p1) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p2 p7 p0 p1 p6 p3 : Prop)
theorem file46_92440 : (((((True → p1) ∧ (p1 ∧ p5)) ∧ ((p0 → False) ∨ (True ∧ p1))) ∧ (((p5 ∨ p7) → (p1 ∨ p2)) → False)) → ((((p5 ∧ p1) ∨ (p0 ∧ p7)) → ((p1 ∧ True) ∨ (p7 ∨ True))) ∨ (((p5 → p3) ∨ (p2 → p6)) ∨ ((p1 ∨ p6) → False)))) := by
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
            apply Or.inl
            intro assump_22
            cases assump_22
            case inl assump_23 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                apply Or.inl
                apply And.intro
                exact assump_26
                apply True.intro
            case inr assump_24 =>
              cases assump_24
              case intro assump_31 assump_32 =>
                apply Or.inl
                apply And.intro
                exact assump_10
                apply True.intro
          case inr assump_17 =>
            cases assump_17
            case intro assump_37 assump_38 =>
              apply Or.inl
              intro assump_45
              cases assump_45
              case inl assump_46 =>
                cases assump_46
                case intro assump_48 assump_49 =>
                  apply Or.inl
                  apply And.intro
                  exact assump_49
                  apply True.intro
              case inr assump_47 =>
                cases assump_47
                case intro assump_54 assump_55 =>
                  apply Or.inl
                  apply And.intro
                  exact assump_38
                  apply True.intro


variable (p5 p6 p2 p4 p0 : Prop)
theorem file46_94270 : ((((((p6 → False) → False) → False) ∨ (((True → False) → (True → False)) → ((p2 ∧ p4) ∧ (p0 ∧ p4)))) ∧ ((((False ∧ p5) ∧ (p6 → False)) → False) ∧ (((True ∨ p2) → (p6 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_34 : ((True ∨ p2) → (p6 → True)) := by
          intro assump_15
          intro assump_16
          apply True.intro
        let assump_14 := assump_9 assump_34
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_3
      case intro assump_22 assump_23 =>
        have assump_35 : ((True ∨ p2) → (p6 → True)) := by
          intro assump_29
          intro assump_30
          apply True.intro
        let assump_28 := assump_23 assump_35
        apply False.elim assump_28


variable (p3 p6 p5 p1 p4 : Prop)
theorem file46_95220 : ((((((p6 ∧ False) ∧ (p3 ∧ p1)) ∧ ((p5 ∨ p4) ∨ (p4 ∧ p3))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p6 ∧ False) ∧ (p3 ∧ p1)) ∧ ((p5 ∨ p4) ∨ (p4 ∧ p3))) → False) := by
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


variable (p0 p3 p2 p6 p5 : Prop)
theorem file46_95775 : ((((((False → False) ∨ (p6 ∨ p2)) → False) → (((p0 ∧ p6) → False) ∨ ((p3 ∨ p5) ∨ (p2 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((False → False) ∨ (p6 ∨ p2)) → False) → (((p0 ∧ p6) → False) ∨ ((p3 ∨ p5) ∨ (p2 ∨ p3)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_28 : ((False → False) ∨ (p6 ∨ p2)) := by
        apply Or.inl
        intro assump_18
        apply False.elim assump_18
      let assump_17 := assump_5 assump_28
      apply False.elim assump_17
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p5 p0 p7 p1 p3 p4 p6 p2 : Prop)
theorem file46_96483 : (((((p6 → p5) ∨ (p4 ∨ p5)) → ((p4 ∧ True) ∨ (False → False))) → (((p3 → False) → (p3 → p7)) ∨ ((True ∧ p3) ∧ (p7 ∧ p2)))) ∨ ((((p5 → False) ∨ (p0 → False)) ∨ ((p2 ∨ p4) → False)) → (((p2 ∨ p7) → False) ∧ ((True ∧ p1) ∧ (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_14 : p3 := by
    exact assump_5
  let assump_10 := assump_4 assump_14
  apply False.elim assump_10


variable (p1 p3 p4 p5 : Prop)
theorem file46_96974 : (((((True → False) ∧ (p1 → False)) ∧ ((p3 ∨ True) ∧ (p3 ∨ p4))) ∧ (((p5 ∨ p4) ∨ (p1 ∧ False)) ∧ ((p1 ∧ True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case inl assump_18 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_24
                  case inl assump_26 =>
                    have assump_180 : True := by
                      apply True.intro
                    let assump_37 := assump_6 assump_180
                    apply False.elim assump_37
                  case inr assump_27 =>
                    have assump_181 : True := by
                      apply True.intro
                    let assump_50 := assump_6 assump_181
                    apply False.elim assump_50
                case inr assump_25 =>
                  cases assump_25
                  case intro assump_54 assump_55 =>
                    apply False.elim assump_55
            case inr assump_19 =>
              cases assump_3
              case intro assump_62 assump_63 =>
                cases assump_62
                case inl assump_64 =>
                  cases assump_64
                  case inl assump_66 =>
                    have assump_182 : True := by
                      apply True.intro
                    let assump_77 := assump_6 assump_182
                    apply False.elim assump_77
                  case inr assump_67 =>
                    have assump_183 : True := by
                      apply True.intro
                    let assump_90 := assump_6 assump_183
                    apply False.elim assump_90
                case inr assump_65 =>
                  cases assump_65
                  case intro assump_94 assump_95 =>
                    apply False.elim assump_95
          case inr assump_15 =>
            cases assump_13
            case inl assump_102 =>
              cases assump_3
              case intro assump_106 assump_107 =>
                cases assump_106
                case inl assump_108 =>
                  cases assump_108
                  case inl assump_110 =>
                    have assump_184 : True := by
                      apply True.intro
                    let assump_120 := assump_6 assump_184
                    apply False.elim assump_120
                  case inr assump_111 =>
                    have assump_185 : True := by
                      apply True.intro
                    let assump_132 := assump_6 assump_185
                    apply False.elim assump_132
                case inr assump_109 =>
                  cases assump_109
                  case intro assump_136 assump_137 =>
                    apply False.elim assump_137
            case inr assump_103 =>
              cases assump_3
              case intro assump_144 assump_145 =>
                cases assump_144
                case inl assump_146 =>
                  cases assump_146
                  case inl assump_148 =>
                    have assump_186 : True := by
                      apply True.intro
                    let assump_158 := assump_6 assump_186
                    apply False.elim assump_158
                  case inr assump_149 =>
                    have assump_187 : True := by
                      apply True.intro
                    let assump_170 := assump_6 assump_187
                    apply False.elim assump_170
                case inr assump_147 =>
                  cases assump_147
                  case intro assump_174 assump_175 =>
                    apply False.elim assump_175


variable (p7 p5 p0 p1 p2 p3 p6 p4 : Prop)
theorem file46_101002 : (((((True ∨ p7) → False) → ((False → p0) ∨ (p2 ∨ p4))) ∨ (((p4 ∧ False) ∧ (p6 → False)) → ((p2 ∧ p6) → False))) ∨ ((((p7 ∧ True) → False) ∧ ((p0 → True) ∧ (p5 ∨ p3))) ∨ (((p3 ∨ False) ∨ (False → False)) → ((p4 ∨ p4) ∨ (p1 → p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p4 p0 p1 p7 p2 p6 p3 p5 : Prop)
theorem file46_101413 : (((((False → p0) → (True ∨ False)) → False) → (((p4 ∨ True) ∨ (p6 ∧ p3)) → False)) ∨ ((((p2 → False) → (p4 ∧ p1)) → ((p5 ∨ p6) ∨ (p3 ∧ p4))) ∨ (((p5 → True) ∧ (True → p3)) ∧ ((p7 → False) → (p3 → p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      have assump_44 : ((False → p0) → (True ∨ False)) := by
        intro assump_12
        apply Or.inl
        apply True.intro
      let assump_11 := assump_1 assump_44
      apply False.elim assump_11
    case inr assump_6 =>
      have assump_45 : ((False → p0) → (True ∨ False)) := by
        intro assump_23
        apply Or.inl
        apply True.intro
      let assump_22 := assump_1 assump_45
      apply False.elim assump_22
  case inr assump_4 =>
    cases assump_4
    case intro assump_29 assump_30 =>
      have assump_46 : ((False → p0) → (True ∨ False)) := by
        intro assump_38
        apply Or.inl
        apply True.intro
      let assump_37 := assump_1 assump_46
      apply False.elim assump_37


variable (p2 p7 p1 p5 : Prop)
theorem file46_102533 : ((((((p5 ∨ p1) → (p2 ∨ True)) → ((False → p7) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p5 ∨ p1) → (p2 ∨ True)) → ((False → p7) → False)) → False) := by
    intro assump_5
    have assump_27 : ((p5 ∨ p1) → (p2 ∨ True)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inr
        apply True.intro
      case inr assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_5 assump_27
    have assump_28 : (False → p7) := by
      intro assump_17
      apply False.elim assump_17
    let assump_16 := assump_8 assump_28
    apply False.elim assump_16
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p1 p3 p5 p0 p7 p2 p6 p4 : Prop)
theorem file46_103325 : (((((p1 → p1) → (p5 → False)) ∨ ((False ∧ p1) ∧ (p7 ∧ p2))) → (((p0 ∨ p6) → False) → ((True → False) → (p5 → p3)))) ∨ ((((True → p3) ∧ (p0 ∨ p3)) → False) → (((p7 → p0) ∧ (p1 → p4)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_1
  case inl assump_11 =>
    have assump_29 : (p1 → p1) := by
      intro assump_16
      exact assump_16
    let assump_15 := assump_11 assump_29
    have assump_30 : p5 := by
      exact assump_4
    let assump_19 := assump_15 assump_30
    apply False.elim assump_19
  case inr assump_12 =>
    cases assump_12
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        apply False.elim assump_25


variable (p2 p0 p5 p7 p4 p1 : Prop)
theorem file46_104132 : (((((p0 ∧ False) ∧ (p0 → False)) → ((p0 ∧ p7) ∧ (p0 ∨ p0))) → False) → ((((p4 ∧ p4) → False) → False) → (((p1 → False) ∧ (p2 ∨ False)) → ((p4 → False) ∨ (p2 → p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      apply Or.inl
      intro assump_16
      have assump_51 : (((p0 ∧ False) ∧ (p0 → False)) → ((p0 ∧ p7) ∧ (p0 ∨ p0))) := by
        intro assump_21
        apply And.intro
        apply And.intro
        cases assump_21
        case intro assump_22 assump_23 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            apply False.elim assump_25
        cases assump_21
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            apply False.elim assump_33
        cases assump_21
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            apply False.elim assump_41
      let assump_20 := assump_1 assump_51
      apply False.elim assump_20
    case inr assump_9 =>
      apply False.elim assump_9


variable (p2 p5 p0 p7 p6 p1 p4 p3 : Prop)
theorem file46_105374 : (((((p5 ∨ p5) ∨ (p4 ∨ True)) → ((p3 → p6) → (False → False))) ∨ (((p5 → p5) ∧ (True ∧ p7)) ∧ ((p1 → False) ∧ (p4 ∧ True)))) ∨ ((((p4 ∧ p7) → (p0 → True)) → ((False ∧ p0) → (p2 → p6))) ∧ (((True ∧ p3) ∨ (True → False)) ∨ ((p1 → p2) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p5 p3 p4 p2 p6 : Prop)
theorem file46_105789 : (((((p6 ∧ p6) → (False → p2)) → False) ∧ (((p2 → False) ∨ (p4 → p2)) ∨ ((p3 → p6) → False))) → ((((False → False) → False) → False) ∨ (((p5 ∨ p5) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        have assump_46 : (False → False) := by
          intro assump_16
          apply False.elim assump_16
        let assump_15 := assump_12 assump_46
        apply False.elim assump_15
      case inr assump_9 =>
        apply Or.inl
        intro assump_24
        have assump_47 : (False → False) := by
          intro assump_28
          apply False.elim assump_28
        let assump_27 := assump_24 assump_47
        apply False.elim assump_27
    case inr assump_7 =>
      apply Or.inl
      intro assump_36
      have assump_48 : (False → False) := by
        intro assump_40
        apply False.elim assump_40
      let assump_39 := assump_36 assump_48
      apply False.elim assump_39


variable (p5 p0 p6 p3 p2 p1 p4 : Prop)
theorem file46_106927 : (((((p0 ∧ p5) → (False → p3)) → False) → False) ∨ ((((p1 ∨ p6) ∨ (p5 → False)) → ((p4 → p4) → (p5 ∧ p1))) ∧ (((p4 → p2) ∨ (p0 ∧ p4)) ∨ ((p4 → False) ∨ (p0 → p2))))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p0 ∧ p5) → (False → p3)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p2 p1 p0 p4 p3 p5 p6 : Prop)
theorem file46_107381 : ((((((p0 ∨ p5) → (p1 ∨ p6)) ∧ ((p2 ∨ p6) → (False ∧ False))) ∧ (((p7 ∨ p4) ∧ (p0 → False)) ∧ ((p2 → p2) → False))) ∨ ((((p6 → p0) → (False ∧ p4)) → False) ∧ (((p1 → p4) → (True ∨ p3)) → False))) → False) := by
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
            cases assump_14
            case inl assump_16 =>
              have assump_57 : (p2 → p2) := by
                intro assump_25
                exact assump_25
              let assump_24 := assump_13 assump_57
              apply False.elim assump_24
            case inr assump_17 =>
              have assump_58 : (p2 → p2) := by
                intro assump_38
                exact assump_38
              let assump_37 := assump_13 assump_58
              apply False.elim assump_37
  case inr assump_3 =>
    cases assump_3
    case intro assump_44 assump_45 =>
      have assump_59 : ((p1 → p4) → (True ∨ p3)) := by
        intro assump_51
        apply Or.inl
        apply True.intro
      let assump_50 := assump_45 assump_59
      apply False.elim assump_50


variable (p3 p1 p5 p6 p0 p7 p2 : Prop)
theorem file46_108743 : ((((((p3 ∧ p5) → False) → False) ∨ (((p0 ∧ True) → False) → False)) ∧ ((((p0 → p6) → False) ∧ ((False ∧ p6) ∧ (p2 → False))) ∧ (((p1 → p5) ∨ (p7 ∧ p7)) → ((p0 ∧ p1) → (p1 ∧ p3))))) → False) := by
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
              apply False.elim assump_16
    case inr assump_5 =>
      cases assump_3
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          cases assump_25
          case intro assump_28 assump_29 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              apply False.elim assump_30


variable (p3 p4 p1 p7 p0 : Prop)
theorem file46_109754 : (((((p0 → p0) ∨ (p3 ∧ p7)) → False) → False) ∨ ((((p4 ∧ p4) → (False → False)) ∨ ((p1 → False) ∨ (p3 ∨ True))) → False)) := by
  apply Or.inl
  intro assump_11
  have assump_21 : ((p0 → p0) ∨ (p3 ∧ p7)) := by
    apply Or.inl
    intro assump_15
    exact assump_15
  let assump_14 := assump_11 assump_21
  apply False.elim assump_14


variable (p7 p2 p6 p0 p5 p1 p3 : Prop)
theorem file46_110151 : (((((False ∨ p3) ∧ (p3 → False)) ∧ ((True ∨ p6) ∧ (p2 → p5))) → (((False → False) → (p0 ∧ p5)) → False)) ∨ ((((p7 → p2) ∨ (p2 → p2)) ∧ ((p5 → p0) ∨ (p6 ∧ p1))) → (((p6 ∨ p2) → False) → ((p3 → False) ∧ (p2 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        cases assump_6
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            have assump_40 : p3 := by
              exact assump_10
            let assump_26 := assump_8 assump_40
            apply False.elim assump_26
          case inr assump_20 =>
            have assump_41 : p3 := by
              exact assump_10
            let assump_36 := assump_8 assump_41
            apply False.elim assump_36


variable (p2 : Prop)
theorem file46_111150 : ((((((p2 ∧ False) → False) → False) → False) → False) → False) := by
  intro assump_24
  have assump_45 : ((((p2 ∧ False) → False) → False) → False) := by
    intro assump_28
    have assump_46 : ((p2 ∧ False) → False) := by
      intro assump_32
      cases assump_32
      case intro assump_33 assump_34 =>
        apply False.elim assump_34
    let assump_31 := assump_28 assump_46
    apply False.elim assump_31
  let assump_27 := assump_24 assump_45
  apply False.elim assump_27


variable (p2 p3 p7 p6 : Prop)
theorem file46_111688 : ((((((p3 ∨ p2) ∧ (p3 ∧ False)) → False) ∨ (((False ∧ p7) ∧ (p6 → p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p3 ∨ p2) ∧ (p3 ∧ False)) → False) ∨ (((False ∧ p7) ∧ (p6 → p3)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
      case inr assump_9 =>
        cases assump_7
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p7 p0 p5 p4 p2 : Prop)
theorem file46_112407 : (((((p1 ∧ False) → False) → False) ∨ (((True → False) ∧ (p1 ∨ False)) ∧ ((p0 ∧ p0) → False))) → ((((p5 ∧ p5) → (p2 → p0)) → ((p2 ∧ p7) → False)) ∨ (((p0 ∨ True) → (p2 ∧ p4)) ∧ ((p5 ∨ p2) ∧ (p0 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      have assump_63 : ((p1 ∧ False) → False) := by
        intro assump_20
        cases assump_20
        case intro assump_21 assump_22 =>
          apply False.elim assump_22
      let assump_19 := assump_2 assump_63
      apply False.elim assump_19
  case inr assump_3 =>
    cases assump_3
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        cases assump_33
        case inl assump_36 =>
          apply Or.inl
          intro assump_42
          intro assump_43
          cases assump_43
          case intro assump_44 assump_45 =>
            have assump_64 : True := by
              apply True.intro
            let assump_57 := assump_32 assump_64
            apply False.elim assump_57
        case inr assump_37 =>
          apply False.elim assump_37


variable (p0 p7 p2 p5 p6 p4 : Prop)
theorem file46_113667 : ((((((False ∨ p7) → False) ∨ ((p6 → False) ∨ (p2 ∧ p7))) ∨ (((p0 → p7) → (p6 → False)) → ((p6 → False) ∨ (True → False)))) ∧ ((((p0 → False) → (p4 → True)) ∨ ((p2 ∧ p5) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_54 : (((p0 → False) → (p4 → True)) ∨ ((p2 ∧ p5) → False)) := by
          apply Or.inl
          intro assump_13
          intro assump_14
          apply True.intro
        let assump_12 := assump_3 assump_54
        apply False.elim assump_12
      case inr assump_7 =>
        cases assump_7
        case inl assump_18 =>
          have assump_55 : (((p0 → False) → (p4 → True)) ∨ ((p2 ∧ p5) → False)) := by
            apply Or.inl
            intro assump_25
            intro assump_26
            apply True.intro
          let assump_24 := assump_3 assump_55
          apply False.elim assump_24
        case inr assump_19 =>
          cases assump_19
          case intro assump_30 assump_31 =>
            have assump_56 : (((p0 → False) → (p4 → True)) ∨ ((p2 ∧ p5) → False)) := by
              apply Or.inl
              intro assump_39
              intro assump_40
              apply True.intro
            let assump_38 := assump_3 assump_56
            apply False.elim assump_38
    case inr assump_5 =>
      have assump_57 : (((p0 → False) → (p4 → True)) ∨ ((p2 ∧ p5) → False)) := by
        apply Or.inl
        intro assump_49
        intro assump_50
        apply True.intro
      let assump_48 := assump_3 assump_57
      apply False.elim assump_48


variable (p3 p6 p5 p2 : Prop)
theorem file46_115378 : ((((((False ∧ False) ∧ (False ∧ p5)) ∨ ((p3 ∧ p6) ∨ (False → False))) ∨ (((p5 ∨ p5) ∨ (p2 ∧ p5)) → ((p6 ∧ p5) ∧ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False ∧ False) ∧ (False ∧ p5)) ∨ ((p3 ∧ p6) ∨ (False → False))) ∨ (((p5 ∨ p5) ∨ (p2 ∧ p5)) → ((p6 ∧ p5) ∧ (False → False)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p2 p3 p7 p5 p6 : Prop)
theorem file46_115929 : (((((p2 → False) → (p7 → p5)) ∧ ((False → False) → False)) → (((p5 ∧ p5) ∨ (p7 ∨ p6)) ∨ ((p5 → p4) → False))) ∨ ((((p7 ∨ p7) → (True → False)) ∨ ((p5 ∨ p7) ∧ (p3 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_8
    have assump_19 : (False → False) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_3 assump_19
    apply False.elim assump_12


variable (p6 p7 : Prop)
theorem file46_116454 : ((((((p6 ∨ p7) ∨ (p7 → True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p6 ∨ p7) ∨ (p7 → True)) → False) → False) := by
    intro assump_5
    have assump_17 : ((p6 ∨ p7) ∨ (p7 → True)) := by
      apply Or.inr
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p0 p7 p3 p1 : Prop)
theorem file46_116940 : (((((p1 → p0) → (True ∧ p1)) → ((p3 ∨ p7) ∧ (False → p0))) ∧ (((True ∨ p0) ∨ (p2 → False)) ∧ ((False → p1) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_45 : (False → p1) := by
            intro assump_17
            apply False.elim assump_17
          let assump_16 := assump_7 assump_45
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_46 : (False → p1) := by
            intro assump_28
            apply False.elim assump_28
          let assump_27 := assump_7 assump_46
          apply False.elim assump_27
      case inr assump_9 =>
        have assump_47 : (False → p1) := by
          intro assump_39
          apply False.elim assump_39
        let assump_38 := assump_7 assump_47
        apply False.elim assump_38


variable (p4 p5 p6 p7 p1 p0 p3 p2 : Prop)
theorem file46_117998 : (((((p5 ∨ p3) → False) → ((p5 → False) → False)) → (((p0 → False) ∨ (p6 → p6)) ∨ ((p4 ∨ p2) ∨ (p6 ∧ True)))) → ((((p1 → False) → False) ∧ ((p3 → False) ∧ (p6 → False))) → (((False → p7) ∧ (False → False)) ∨ ((p1 ∨ p4) ∧ (p1 ∨ p6))))) := by
  intro assump_7
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_10
    case intro assump_13 assump_14 =>
      apply Or.inl
      apply And.intro
      intro assump_21
      apply False.elim assump_21
      intro assump_24
      apply False.elim assump_24


variable (p7 p0 p5 p1 p3 p2 : Prop)
theorem file46_118593 : (((((p5 → False) → (True → True)) ∧ ((p7 → True) → False)) ∧ (((p3 → False) ∨ (p1 ∨ p0)) ∧ ((p7 → False) ∨ (p2 ∧ p2)))) → ((((p0 ∨ False) → (p3 ∧ p7)) → False) ∨ (((True → p3) → False) → False))) := by
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
          case inl assump_16 =>
            apply Or.inl
            intro assump_20
            have assump_127 : (p7 → True) := by
              intro assump_27
              apply True.intro
            let assump_26 := assump_5 assump_127
            apply False.elim assump_26
          case inr assump_17 =>
            cases assump_17
            case intro assump_31 assump_32 =>
              apply Or.inl
              intro assump_37
              have assump_128 : (p7 → True) := by
                intro assump_45
                apply True.intro
              let assump_44 := assump_5 assump_128
              apply False.elim assump_44
        case inr assump_13 =>
          cases assump_13
          case inl assump_49 =>
            cases assump_11
            case inl assump_53 =>
              apply Or.inl
              intro assump_57
              have assump_129 : (p7 → True) := by
                intro assump_64
                apply True.intro
              let assump_63 := assump_5 assump_129
              apply False.elim assump_63
            case inr assump_54 =>
              cases assump_54
              case intro assump_68 assump_69 =>
                apply Or.inl
                intro assump_74
                have assump_130 : (p7 → True) := by
                  intro assump_82
                  apply True.intro
                let assump_81 := assump_5 assump_130
                apply False.elim assump_81
          case inr assump_50 =>
            cases assump_11
            case inl assump_88 =>
              apply Or.inl
              intro assump_92
              have assump_131 : (p7 → True) := by
                intro assump_102
                apply True.intro
              let assump_101 := assump_5 assump_131
              apply False.elim assump_101
            case inr assump_89 =>
              cases assump_89
              case intro assump_106 assump_107 =>
                apply Or.inl
                intro assump_112
                have assump_132 : (p7 → True) := by
                  intro assump_123
                  apply True.intro
                let assump_122 := assump_5 assump_132
                apply False.elim assump_122


variable (p1 p2 p5 p4 p7 p6 : Prop)
theorem file46_121332 : (((((p4 ∧ p7) ∧ (p6 → False)) ∨ ((p5 ∧ p4) → False)) → (((p2 ∧ p7) ∧ (True → False)) → False)) ∨ ((((p2 ∧ p6) → False) ∨ ((p1 ∧ p5) ∧ (p2 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            have assump_39 : True := by
              apply True.intro
            let assump_28 := assump_4 assump_39
            apply False.elim assump_28
      case inr assump_14 =>
        have assump_40 : True := by
          apply True.intro
        let assump_35 := assump_4 assump_40
        apply False.elim assump_35


variable (p7 p1 p4 p3 p2 p0 p5 p6 : Prop)
theorem file46_122231 : (((((True → False) → False) → ((p0 ∨ True) ∨ (p5 → True))) ∨ (((p2 → False) ∧ (p1 → False)) → False)) ∨ ((((p3 ∨ p7) ∨ (True ∨ p3)) ∧ ((p4 ∧ p5) → (p7 ∧ p1))) → (((p4 → False) → False) ∨ ((p2 → p6) ∧ (p1 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_17
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p2 p1 : Prop)
theorem file46_122599 : ((((((p1 → False) → (p1 → p2)) → False) → (((p1 → False) ∧ (False → False)) → False)) → False) → False) := by
  intro assump_14
  have assump_45 : ((((p1 → False) → (p1 → p2)) → False) → (((p1 → False) ∧ (False → False)) → False)) := by
    intro assump_18
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      have assump_46 : ((p1 → False) → (p1 → p2)) := by
        intro assump_29
        intro assump_30
        have assump_47 : p1 := by
          exact assump_30
        let assump_35 := assump_29 assump_47
        apply False.elim assump_35
      let assump_28 := assump_18 assump_46
      apply False.elim assump_28
  let assump_17 := assump_14 assump_45
  apply False.elim assump_17


variable (p4 p5 p1 p3 : Prop)
theorem file46_123376 : (((((False → False) ∨ (p3 → p5)) → False) → False) ∨ ((((p5 ∨ p4) ∧ (p3 ∧ p1)) ∨ ((p1 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (p3 → p5)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p6 p5 p1 : Prop)
theorem file46_123769 : (((((p6 → False) → (p6 → False)) ∨ ((p1 ∨ p5) ∨ (p2 → p1))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p6 → False) → (p6 → False)) ∨ ((p1 ∨ p5) ∨ (p2 → p1))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : p6 := by
      exact assump_6
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p4 p5 p7 p0 p2 : Prop)
theorem file46_124255 : (((((p2 ∨ p3) → False) ∨ ((p7 ∨ p5) → False)) ∧ (((p0 ∧ p3) ∧ (p0 → False)) ∨ ((True ∨ p4) ∧ (p4 ∧ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_82 : p0 := by
              exact assump_12
            let assump_20 := assump_11 assump_82
            apply False.elim assump_20
      case inr assump_9 =>
        cases assump_9
        case intro assump_24 assump_25 =>
          cases assump_24
          case inl assump_26 =>
            cases assump_25
            case intro assump_30 assump_31 =>
              apply False.elim assump_31
          case inr assump_27 =>
            cases assump_25
            case intro assump_38 assump_39 =>
              apply False.elim assump_39
    case inr assump_5 =>
      cases assump_3
      case inl assump_46 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          cases assump_48
          case intro assump_50 assump_51 =>
            have assump_83 : p0 := by
              exact assump_50
            let assump_58 := assump_49 assump_83
            apply False.elim assump_58
      case inr assump_47 =>
        cases assump_47
        case intro assump_62 assump_63 =>
          cases assump_62
          case inl assump_64 =>
            cases assump_63
            case intro assump_68 assump_69 =>
              apply False.elim assump_69
          case inr assump_65 =>
            cases assump_63
            case intro assump_76 assump_77 =>
              apply False.elim assump_77


variable (p2 p0 p1 p6 p5 p3 : Prop)
theorem file46_126082 : (((((p2 → False) ∧ (p6 → p6)) → ((True → p2) ∨ (p5 ∧ False))) → (((True → False) ∨ (True ∨ True)) ∧ ((p3 ∨ p3) → False))) → ((((True → False) ∧ (p1 → True)) → False) ∨ (((p1 → False) → (p0 ∧ p2)) ∧ ((p3 ∧ p0) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_16 : True := by
      apply True.intro
    let assump_12 := assump_5 assump_16
    apply False.elim assump_12


variable (p7 p3 p2 p0 p1 p6 p5 : Prop)
theorem file46_126598 : (((((p6 → p1) → (p1 → p7)) ∨ ((p5 ∧ p2) ∨ (p3 ∧ p5))) → (((p6 → True) ∨ (p7 → False)) ∨ ((p0 → p7) → (False ∨ p6)))) ∨ ((((p2 ∧ p2) → False) ∨ ((p7 → p0) → False)) ∨ (((p3 ∨ p1) ∧ (p7 ∨ p1)) ∧ ((p6 ∨ p7) ∨ (False ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply Or.inl
        apply Or.inl
        intro assump_15
        apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_16 assump_17 =>
        apply Or.inl
        apply Or.inl
        intro assump_22
        apply True.intro


variable (p7 p2 p0 p1 p6 : Prop)
theorem file46_127425 : ((((((True → False) → (p1 → False)) → ((p2 ∨ p2) → (p0 → False))) → (((p6 ∨ p0) → (False → True)) ∧ ((p1 ∧ False) → (False ∧ p2)))) ∧ ((((p0 ∧ p6) ∧ (p7 ∧ p1)) → ((True ∧ p2) ∨ (True ∨ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_27 : (((p0 ∧ p6) ∧ (p7 ∧ p1)) → ((True ∧ p2) ∨ (True ∨ p0))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply Or.inr
            apply Or.inl
            apply True.intro
    let assump_8 := assump_3 assump_27
    apply False.elim assump_8


variable (p7 p6 p5 p3 p1 : Prop)
theorem file46_128215 : (((((p7 → False) ∧ (False ∧ p6)) ∧ ((p3 → True) → (True → p5))) ∨ (((p1 ∧ p5) → (p3 → p3)) ∧ ((False → p1) ∧ (False ∨ False)))) → False) := by
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_20
        case intro assump_23 assump_24 =>
          apply False.elim assump_23
  case inr assump_16 =>
    cases assump_16
    case intro assump_27 assump_28 =>
      cases assump_28
      case intro assump_31 assump_32 =>
        cases assump_32
        case inl assump_35 =>
          apply False.elim assump_35
        case inr assump_36 =>
          apply False.elim assump_36


variable (p4 p0 p6 p3 p7 p5 : Prop)
theorem file46_129003 : ((((((p3 ∧ True) → False) → False) → (((p7 → False) ∧ (p6 → False)) ∨ ((p6 ∨ p3) ∧ (False → False)))) ∧ ((((False ∧ p0) → (True ∨ p4)) ∨ ((p5 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((False ∧ p0) → (True ∨ p4)) ∨ ((p5 → False) → False)) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p4 p0 p2 p5 p3 p1 p6 : Prop)
theorem file46_129608 : ((((((p4 ∨ p3) → (p1 ∨ p6)) → False) ∨ (((p5 → False) ∨ (p0 ∨ True)) → False)) ∧ ((((p0 ∧ p5) → False) ∧ ((p5 ∧ p0) → False)) ∧ (((p5 → False) → False) ∧ ((p2 → p4) ∧ (True ∧ False))))) → False) := by
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
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                apply False.elim assump_25
    case inr assump_5 =>
      cases assump_3
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          cases assump_33
          case intro assump_40 assump_41 =>
            cases assump_41
            case intro assump_44 assump_45 =>
              cases assump_45
              case intro assump_48 assump_49 =>
                apply False.elim assump_49


variable (p4 p7 p2 p0 p3 : Prop)
theorem file46_130783 : ((((((True ∨ p3) → (p7 ∧ p2)) → ((p0 ∧ False) → (p0 ∧ False))) ∨ (((p7 → p4) → False) ∨ ((p0 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((True ∨ p3) → (p7 ∧ p2)) → ((p0 ∧ False) → (p0 ∧ False))) ∨ (((p7 → p4) → False) ∨ ((p0 → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
    cases assump_6
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 : Prop)
theorem file46_131435 : (((((p0 → True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : (((p0 → True) → False) → False) := by
    intro assump_5
    have assump_17 : (p0 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p1 p0 p2 p3 p4 p7 p6 p5 : Prop)
theorem file46_131869 : (((((p7 ∧ p7) ∨ (p1 ∧ True)) → ((p4 → p2) ∧ (p2 → p1))) → (((p5 ∧ p6) → False) ∨ ((True ∧ p4) ∨ (False → True)))) → ((((p3 → False) ∧ (p0 → p3)) ∧ ((False ∧ p7) ∧ (p3 → False))) → (((False ∨ p4) ∧ (p4 → p0)) ∨ ((p2 ∧ p2) → (p1 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13


variable (p3 p5 p1 p4 p7 p2 p0 p6 : Prop)
theorem file46_132485 : (((((p4 → False) ∧ (False ∨ p0)) ∧ ((p2 ∨ p7) → (p5 → False))) → False) → ((((p7 → p5) ∨ (p0 → p4)) → ((p6 → False) ∨ (False → False))) → (((p3 → p3) ∨ (p6 ∨ p5)) ∨ ((p7 → False) ∨ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  intro assump_7
  exact assump_7


variable (p4 p1 p5 p3 p6 : Prop)
theorem file46_132844 : ((((((False → p1) → False) → ((p4 → False) ∨ (p3 → False))) ∨ (((p6 → p5) → False) ∧ ((True → False) ∧ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False → p1) → False) → ((p4 → False) ∨ (p3 → False))) ∨ (((p6 → p5) → False) ∧ ((True → False) ∧ (p1 → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_23 : (False → p1) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


