variable (p5 p3 p4 p0 p6 p1 p7 p2 : Prop)
theorem file98_50 : ((((((p2 → False) → False) ∨ ((p0 ∨ False) → False)) ∨ (((p1 ∨ p6) ∧ (True ∧ p7)) ∧ ((False → p4) → (p4 → p7)))) ∧ ((((p6 ∧ True) ∨ (p5 → p7)) → False) ∧ (((p1 ∧ p3) ∧ (False ∧ p0)) ∧ ((p2 → p5) → (p0 → p4))))) → False) := by
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
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_17
                case intro assump_24 assump_25 =>
                  apply False.elim assump_24
      case inr assump_7 =>
        cases assump_3
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              cases assump_36
              case intro assump_38 assump_39 =>
                cases assump_37
                case intro assump_44 assump_45 =>
                  apply False.elim assump_44
    case inr assump_5 =>
      cases assump_5
      case intro assump_48 assump_49 =>
        cases assump_48
        case intro assump_50 assump_51 =>
          cases assump_50
          case inl assump_52 =>
            cases assump_51
            case intro assump_56 assump_57 =>
              cases assump_3
              case intro assump_64 assump_65 =>
                cases assump_65
                case intro assump_68 assump_69 =>
                  cases assump_68
                  case intro assump_70 assump_71 =>
                    cases assump_70
                    case intro assump_72 assump_73 =>
                      cases assump_71
                      case intro assump_78 assump_79 =>
                        apply False.elim assump_78
          case inr assump_53 =>
            cases assump_51
            case intro assump_84 assump_85 =>
              cases assump_3
              case intro assump_92 assump_93 =>
                cases assump_93
                case intro assump_96 assump_97 =>
                  cases assump_96
                  case intro assump_98 assump_99 =>
                    cases assump_98
                    case intro assump_100 assump_101 =>
                      cases assump_99
                      case intro assump_106 assump_107 =>
                        apply False.elim assump_106


variable (p6 p1 p2 p3 p7 p4 : Prop)
theorem file98_2706 : (((((False → False) → (p7 → p4)) → False) ∧ (((False ∨ p1) ∨ (p6 ∧ p3)) ∧ ((True ∨ p7) → False))) → ((((False ∧ p3) → (False ∧ p6)) → ((p2 → False) ∧ (p4 → p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply False.elim assump_13
        case inr assump_14 =>
          have assump_37 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_21 := assump_10 assump_37
          apply False.elim assump_21
      case inr assump_12 =>
        cases assump_12
        case intro assump_25 assump_26 =>
          have assump_38 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_33 := assump_10 assump_38
          apply False.elim assump_33


variable (p5 p3 p4 p2 p0 p1 p6 p7 : Prop)
theorem file98_3721 : (((((False → False) ∧ (True ∨ p2)) ∨ ((p0 ∨ p5) ∨ (p7 → False))) → False) → ((((p6 → False) ∨ (p4 ∨ False)) → False) ∧ (((p2 ∧ p2) → (p3 ∨ p1)) ∨ ((p7 → p7) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_49 : (((False → False) ∧ (True ∨ p2)) ∨ ((p0 ∨ p5) ∨ (p7 → False))) := by
      apply Or.inl
      apply And.intro
      intro assump_10
      apply False.elim assump_10
      apply Or.inl
      apply True.intro
    let assump_9 := assump_1 assump_49
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case inl assump_16 =>
      have assump_50 : (((False → False) ∧ (True ∨ p2)) ∨ ((p0 ∨ p5) ∨ (p7 → False))) := by
        apply Or.inl
        apply And.intro
        intro assump_23
        apply False.elim assump_23
        apply Or.inl
        apply True.intro
      let assump_22 := assump_1 assump_50
      apply False.elim assump_22
    case inr assump_17 =>
      apply False.elim assump_17
  apply Or.inl
  intro assump_33
  cases assump_33
  case intro assump_34 assump_35 =>
    have assump_51 : (((False → False) ∧ (True ∨ p2)) ∨ ((p0 ∨ p5) ∨ (p7 → False))) := by
      apply Or.inl
      apply And.intro
      intro assump_43
      apply False.elim assump_43
      apply Or.inl
      apply True.intro
    let assump_42 := assump_1 assump_51
    apply False.elim assump_42


variable (p7 p6 : Prop)
theorem file98_5163 : ((((((p6 → False) → (p7 → False)) ∧ ((False → True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p6 → False) → (p7 → False)) ∧ ((False → True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : (False → True) := by
        intro assump_13
        apply True.intro
      let assump_12 := assump_7 assump_21
      apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p4 p1 p5 p2 p0 p6 p7 p3 : Prop)
theorem file98_5742 : (((((p2 ∧ p3) → (p6 ∨ p3)) ∧ ((p7 → p7) ∧ (p4 ∧ p7))) ∧ (((p1 ∧ p5) ∨ (True ∨ p3)) → False)) → ((((p1 → False) → (p0 → False)) → ((p0 ∨ True) ∧ (p0 ∨ p0))) ∧ (((p1 ∨ p6) → False) ∨ ((p5 ∨ p1) ∨ (p7 → p0))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply Or.inr
          apply True.intro
  cases assump_1
  case intro assump_25 assump_26 =>
    cases assump_25
    case intro assump_27 assump_28 =>
      cases assump_28
      case intro assump_31 assump_32 =>
        cases assump_32
        case intro assump_35 assump_36 =>
          have assump_82 : ((p1 ∧ p5) ∨ (True ∨ p3)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_43 := assump_26 assump_82
          apply False.elim assump_43
  cases assump_1
  case intro assump_47 assump_48 =>
    cases assump_47
    case intro assump_49 assump_50 =>
      cases assump_50
      case intro assump_53 assump_54 =>
        cases assump_54
        case intro assump_57 assump_58 =>
          apply Or.inl
          intro assump_65
          cases assump_65
          case inl assump_66 =>
            have assump_83 : ((p1 ∧ p5) ∨ (True ∨ p3)) := by
              apply Or.inr
              apply Or.inl
              apply True.intro
            let assump_71 := assump_48 assump_83
            apply False.elim assump_71
          case inr assump_67 =>
            have assump_84 : ((p1 ∧ p5) ∨ (True ∨ p3)) := by
              apply Or.inr
              apply Or.inl
              apply True.intro
            let assump_78 := assump_48 assump_84
            apply False.elim assump_78


variable (p1 p3 p4 p2 p5 : Prop)
theorem file98_7673 : ((((((p5 ∧ p5) → False) → ((p1 ∨ True) ∧ (p3 → False))) → (((p2 ∨ p4) → (True → p2)) → ((p4 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p5 ∧ p5) → False) → ((p1 ∨ True) ∧ (p3 → False))) → (((p2 ∨ p4) → (True → p2)) → ((p4 ∧ False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p0 p2 : Prop)
theorem file98_8221 : (((((True → False) → False) → ((p0 → True) ∨ (p5 ∨ p2))) → False) → False) := by
  intro assump_23
  have assump_34 : (((True → False) → False) → ((p0 → True) ∨ (p5 ∨ p2))) := by
    intro assump_27
    apply Or.inl
    intro assump_30
    apply True.intro
  let assump_26 := assump_23 assump_34
  apply False.elim assump_26


variable (p6 p1 p3 p0 p2 p7 : Prop)
theorem file98_8606 : (((((p3 ∧ p7) ∨ (p7 ∨ p1)) ∧ ((p0 ∨ p2) → (p3 ∨ p0))) ∨ (((p1 ∨ p7) → False) → ((True → False) → False))) ∨ ((((p6 → p7) ∨ (False ∨ p3)) ∨ ((p2 → False) → (False → False))) → False)) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  have assump_12 : True := by
    apply True.intro
  let assump_8 := assump_2 assump_12
  apply False.elim assump_8


variable (p0 p6 p2 p7 p3 p5 p4 : Prop)
theorem file98_9038 : (((((p3 ∨ p5) → (p4 ∧ p2)) ∧ ((True → p7) ∨ (p0 ∨ p7))) → (((True ∧ False) → False) ∨ ((p6 → False) → False))) → ((((p4 → False) → False) → ((p3 → p3) → (False → False))) ∨ (((p5 ∨ p4) → (p5 ∨ p5)) → ((p2 → False) ∨ (True ∧ False))))) := by
  intro assump_11
  apply Or.inl
  intro assump_14
  intro assump_15
  intro assump_16
  apply False.elim assump_16


variable (p1 p6 p3 p2 p0 p5 : Prop)
theorem file98_9455 : ((((((p0 → False) → (p3 → False)) → ((p6 ∨ False) → (True ∨ p2))) → False) ∧ ((((p3 ∨ False) ∨ (p5 → True)) ∨ ((p0 ∨ p1) ∨ (p0 ∨ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (((p3 ∨ False) ∨ (p5 → True)) ∨ ((p0 ∨ p1) ∨ (p0 ∨ p5))) := by
      apply Or.inl
      apply Or.inr
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p0 p6 p5 p4 p3 p7 p1 : Prop)
theorem file98_9981 : (((((p5 ∨ False) ∨ (p4 → p0)) ∧ ((False → p1) ∧ (p3 ∧ p7))) → False) → ((((p6 → p7) ∨ (True → p6)) → ((p1 ∧ p4) ∨ (False → False))) ∧ (((p3 ∨ p1) ∧ (False ∧ p0)) ∨ ((True ∨ p0) ∨ (p3 ∨ p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inr
    intro assump_9
    apply False.elim assump_9
  case inr assump_4 =>
    apply Or.inr
    intro assump_16
    apply False.elim assump_16
  apply Or.inr
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p7 p5 p0 p6 p2 p3 : Prop)
theorem file98_10553 : (((((False ∨ p6) ∧ (p5 → p7)) ∨ ((p2 → True) → False)) → (((False ∨ p0) → False) → ((True → True) ∨ (p5 → p5)))) ∨ ((((False → False) ∧ (p3 ∨ p6)) → ((p2 → p0) → (p6 → p6))) → False)) := by
  apply Or.inl
  intro assump_12
  intro assump_13
  cases assump_12
  case inl assump_16 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_18
      case inl assump_20 =>
        apply False.elim assump_20
      case inr assump_21 =>
        apply Or.inl
        intro assump_28
        apply True.intro
  case inr assump_17 =>
    apply Or.inl
    intro assump_31
    apply True.intro


variable (p4 p5 p3 p0 p2 : Prop)
theorem file98_11216 : ((((((p2 ∧ p3) → (p2 → p2)) → False) → (((p5 → False) → (p4 → False)) ∧ ((p0 → False) → False))) → False) → False) := by
  intro assump_7
  have assump_56 : ((((p2 ∧ p3) → (p2 → p2)) → False) → (((p5 → False) → (p4 → False)) ∧ ((p0 → False) → False))) := by
    intro assump_11
    apply And.intro
    intro assump_12
    intro assump_13
    have assump_57 : ((p2 ∧ p3) → (p2 → p2)) := by
      intro assump_21
      intro assump_22
      cases assump_21
      case intro assump_25 assump_26 =>
        exact assump_25
    let assump_20 := assump_11 assump_57
    apply False.elim assump_20
    intro assump_34
    have assump_58 : ((p2 ∧ p3) → (p2 → p2)) := by
      intro assump_40
      intro assump_41
      cases assump_40
      case intro assump_44 assump_45 =>
        exact assump_44
    let assump_39 := assump_11 assump_58
    apply False.elim assump_39
  let assump_10 := assump_7 assump_56
  apply False.elim assump_10


variable (p4 p1 p6 p2 p0 p5 p7 p3 : Prop)
theorem file98_12213 : (((((p6 → False) → (p3 → False)) → ((p7 → False) → False)) → (((p6 → False) ∧ (p3 ∨ p7)) → ((p5 ∨ False) → (p4 → p4)))) ∨ ((((p6 ∨ p7) → (p2 → False)) → ((p5 ∧ p0) ∧ (p2 ∨ p3))) ∧ (((p0 → p6) ∧ (p1 ∧ p7)) ∧ ((p3 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_2
    case intro assump_11 assump_12 =>
      cases assump_12
      case inl assump_15 =>
        exact assump_4
      case inr assump_16 =>
        exact assump_4
  case inr assump_8 =>
    apply False.elim assump_8


variable (p6 p0 p3 p5 p7 p4 : Prop)
theorem file98_12869 : ((((((p7 ∧ False) ∨ (False → False)) ∧ ((True ∧ p0) → False)) → (((p7 ∧ False) → False) → False)) ∧ ((((p6 ∨ True) ∨ (p3 ∧ p4)) ∨ ((p6 ∧ p0) ∧ (p3 ∧ p5))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_16 : (((p6 ∨ True) ∨ (p3 ∧ p4)) ∨ ((p6 ∧ p0) ∧ (p3 ∧ p5))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_12 := assump_7 assump_16
    apply False.elim assump_12


variable (p6 p4 p1 p2 : Prop)
theorem file98_13403 : (((((p1 → False) → (p1 ∨ p2)) → ((p4 ∧ p1) ∨ (p6 → p6))) ∨ (((p2 → True) → False) → ((False → True) → (p2 ∨ p1)))) ∨ ((((p6 ∨ p6) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  exact assump_4


variable (p4 p6 p2 p5 p7 p1 p3 : Prop)
theorem file98_13726 : (((((p3 ∧ p3) → (p6 ∨ p4)) → False) → (((False ∧ p6) ∧ (p4 → p7)) → False)) ∨ ((((p1 → False) → False) → False) ∨ (((p5 ∨ p2) ∨ (p2 ∧ True)) ∨ ((False ∨ False) → (p2 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p1 p7 p3 p0 p2 p4 : Prop)
theorem file98_14155 : ((((((p4 ∨ False) ∧ (p4 → False)) → False) ∧ (((p0 → False) ∧ (True ∨ p4)) → False)) ∧ ((((p4 → p2) → False) ∧ ((p3 ∨ p3) ∧ (p1 ∨ p1))) ∧ (((False ∨ p3) → False) ∧ ((p2 ∧ p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_17
              case inl assump_22 =>
                cases assump_11
                case intro assump_26 assump_27 =>
                  have assump_80 : (False ∨ p3) := by
                    apply Or.inr
                    exact assump_18
                  let assump_33 := assump_26 assump_80
                  apply False.elim assump_33
              case inr assump_23 =>
                cases assump_11
                case intro assump_39 assump_40 =>
                  have assump_81 : (False ∨ p3) := by
                    apply Or.inr
                    exact assump_18
                  let assump_46 := assump_39 assump_81
                  apply False.elim assump_46
            case inr assump_19 =>
              cases assump_17
              case inl assump_52 =>
                cases assump_11
                case intro assump_56 assump_57 =>
                  have assump_82 : (False ∨ p3) := by
                    apply Or.inr
                    exact assump_19
                  let assump_63 := assump_56 assump_82
                  apply False.elim assump_63
              case inr assump_53 =>
                cases assump_11
                case intro assump_69 assump_70 =>
                  have assump_83 : (False ∨ p3) := by
                    apply Or.inr
                    exact assump_19
                  let assump_76 := assump_69 assump_83
                  apply False.elim assump_76


variable (p3 p4 p7 p6 p5 p0 p2 : Prop)
theorem file98_16260 : ((((((p3 ∨ False) ∨ (p5 → True)) → False) → (((p0 ∨ p4) → False) ∨ ((p0 → False) → (p3 → False)))) ∧ ((((False ∧ p2) → (p4 ∧ p7)) ∨ ((p2 ∨ False) ∨ (p6 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((False ∧ p2) → (p4 ∧ p7)) ∨ ((p2 ∨ False) ∨ (p6 → p7))) := by
      apply Or.inl
      intro assump_9
      apply And.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
      cases assump_9
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p0 p6 p7 p3 p5 p2 p1 : Prop)
theorem file98_16984 : (((((p1 → False) → False) ∨ ((p6 ∨ True) ∧ (p3 → False))) → False) → ((((p7 ∨ p0) → (p3 ∨ p6)) → ((p2 ∧ p1) ∨ (p1 → p6))) ∨ (((p5 → False) ∨ (p6 ∨ p1)) ∧ ((True ∧ True) ∧ (p0 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inr
  intro assump_7
  have assump_23 : (((p1 → False) → False) ∨ ((p6 ∨ True) ∧ (p3 → False))) := by
    apply Or.inl
    intro assump_13
    have assump_24 : p1 := by
      exact assump_7
    let assump_16 := assump_13 assump_24
    apply False.elim assump_16
  let assump_12 := assump_1 assump_23
  apply False.elim assump_12


variable (p6 p0 : Prop)
theorem file98_17615 : (((((True → False) ∧ (p6 ∨ p0)) → False) → False) → False) := by
  intro assump_1
  have assump_29 : (((True → False) ∧ (p6 ∨ p0)) → False) := by
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


variable (p5 p2 p6 p4 p7 p1 : Prop)
theorem file98_18321 : (((((p4 ∧ p1) ∨ (True ∨ p6)) → False) ∧ (((p5 ∧ p4) → False) ∨ ((p7 → p6) ∧ (p2 → p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_27 : ((p4 ∧ p1) ∨ (True ∨ p6)) := by
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_11 := assump_2 assump_27
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_15 assump_16 =>
        have assump_28 : ((p4 ∧ p1) ∨ (True ∨ p6)) := by
          apply Or.inr
          apply Or.inl
          apply True.intro
        let assump_23 := assump_2 assump_28
        apply False.elim assump_23


variable (p0 p1 p2 p6 p7 : Prop)
theorem file98_19086 : ((((((p7 ∨ True) → False) → ((p0 → p1) → (p1 ∧ p7))) ∨ (((p0 ∨ p2) ∧ (p6 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p7 ∨ True) → False) → ((p0 → p1) → (p1 ∧ p7))) ∨ (((p0 ∨ p2) ∧ (p6 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply And.intro
    have assump_27 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_11 := assump_5 assump_27
    apply False.elim assump_11
    have assump_28 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_19 := assump_5 assump_28
    apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p1 p6 p3 : Prop)
theorem file98_19831 : ((((((True → False) → (p1 ∧ p1)) → False) → (((p6 → True) ∧ (p3 → p1)) → False)) → False) → False) := by
  intro assump_41
  have assump_75 : ((((True → False) → (p1 ∧ p1)) → False) → (((p6 → True) ∧ (p3 → p1)) → False)) := by
    intro assump_45
    intro assump_46
    cases assump_46
    case intro assump_47 assump_48 =>
      have assump_76 : ((True → False) → (p1 ∧ p1)) := by
        intro assump_56
        apply And.intro
        have assump_77 : True := by
          apply True.intro
        let assump_59 := assump_56 assump_77
        apply False.elim assump_59
        have assump_78 : True := by
          apply True.intro
        let assump_65 := assump_56 assump_78
        apply False.elim assump_65
      let assump_55 := assump_45 assump_76
      apply False.elim assump_55
  let assump_44 := assump_41 assump_75
  apply False.elim assump_44


variable (p0 p4 p7 p2 p1 p3 p5 p6 : Prop)
theorem file98_20758 : ((((((True → p2) ∧ (p7 ∨ p3)) ∨ ((p6 ∧ p1) ∧ (p7 ∧ p5))) ∧ (((True → p3) ∧ (p5 → p4)) ∧ ((p7 ∧ False) ∧ (p2 → p2)))) ∧ ((((p0 → False) → (p1 → p4)) → False) → False)) → False) := by
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
          case inl assump_12 =>
            cases assump_5
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_17
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    apply False.elim assump_27
          case inr assump_13 =>
            cases assump_5
            case intro assump_34 assump_35 =>
              cases assump_34
              case intro assump_36 assump_37 =>
                cases assump_35
                case intro assump_42 assump_43 =>
                  cases assump_42
                  case intro assump_44 assump_45 =>
                    apply False.elim assump_45
      case inr assump_7 =>
        cases assump_7
        case intro assump_50 assump_51 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            cases assump_51
            case intro assump_58 assump_59 =>
              cases assump_5
              case intro assump_64 assump_65 =>
                cases assump_64
                case intro assump_66 assump_67 =>
                  cases assump_65
                  case intro assump_72 assump_73 =>
                    cases assump_72
                    case intro assump_74 assump_75 =>
                      apply False.elim assump_75


variable (p4 p6 p3 p0 p2 : Prop)
theorem file98_22672 : ((((((p6 → True) ∨ (p2 → p0)) → False) → (((p3 → p4) ∨ (True → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p6 → True) ∨ (p2 → p0)) → False) → (((p3 → p4) ∨ (True → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_31 : ((p6 → True) ∨ (p2 → p0)) := by
        apply Or.inl
        intro assump_14
        apply True.intro
      let assump_13 := assump_5 assump_31
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_32 : ((p6 → True) ∨ (p2 → p0)) := by
        apply Or.inl
        intro assump_23
        apply True.intro
      let assump_22 := assump_5 assump_32
      apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p3 p5 p1 p4 p2 p7 p0 p6 : Prop)
theorem file98_23536 : (((((p7 ∧ p6) ∧ (p4 ∧ p6)) ∨ ((p3 ∧ p3) → False)) → (((True → False) → (p5 ∨ p2)) → False)) → ((((p3 → False) → (p0 → p1)) ∨ ((p6 → False) ∧ (p1 ∧ True))) → (((p7 ∧ False) → (p6 ∨ p3)) ∨ ((p7 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  case inr assump_4 =>
    cases assump_4
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        apply Or.inl
        intro assump_28
        cases assump_28
        case intro assump_29 assump_30 =>
          apply False.elim assump_30


variable (p0 p5 p6 p7 p1 p4 p2 : Prop)
theorem file98_24308 : (((((True → False) → (False ∧ p5)) → False) → (((p0 → p1) ∨ (p6 → False)) → False)) ∨ ((((p2 → p4) → False) ∨ ((True ∨ p2) → False)) → (((p1 → p7) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_47 : ((True → False) → (False ∧ p5)) := by
      intro assump_10
      apply And.intro
      have assump_48 : True := by
        apply True.intro
      let assump_13 := assump_10 assump_48
      apply False.elim assump_13
      have assump_49 : True := by
        apply True.intro
      let assump_19 := assump_10 assump_49
      apply False.elim assump_19
    let assump_9 := assump_1 assump_47
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_50 : ((True → False) → (False ∧ p5)) := by
      intro assump_31
      apply And.intro
      have assump_51 : True := by
        apply True.intro
      let assump_34 := assump_31 assump_51
      apply False.elim assump_34
      have assump_52 : True := by
        apply True.intro
      let assump_40 := assump_31 assump_52
      apply False.elim assump_40
    let assump_30 := assump_1 assump_50
    apply False.elim assump_30


variable (p7 p2 p4 p5 p3 p0 p6 : Prop)
theorem file98_25542 : ((((((p3 ∧ p6) ∨ (False → p0)) ∨ ((p7 ∧ p6) ∨ (p0 → p5))) → False) ∨ ((((p7 → False) ∧ (p2 → False)) → ((p2 ∧ p4) ∨ (True ∨ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_26 : (((p3 ∧ p6) ∨ (False → p0)) ∨ ((p7 ∧ p6) ∨ (p0 → p5))) := by
      apply Or.inl
      apply Or.inr
      intro assump_7
      apply False.elim assump_7
    let assump_6 := assump_2 assump_26
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_27 : (((p7 → False) ∧ (p2 → False)) → ((p2 ∧ p4) ∨ (True ∨ p7))) := by
      intro assump_16
      cases assump_16
      case intro assump_17 assump_18 =>
        apply Or.inr
        apply Or.inl
        apply True.intro
    let assump_15 := assump_3 assump_27
    apply False.elim assump_15


variable (p4 p2 p5 p1 p0 p6 p3 : Prop)
theorem file98_26391 : (((((p3 → p6) → False) → ((p2 ∧ True) ∨ (True ∨ True))) → False) → ((((True ∨ p3) → False) ∧ ((True → False) → False)) ∨ (((p4 ∨ p0) ∧ (False → p3)) ∧ ((p5 → p1) ∧ (p3 ∧ p3))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_33 : (((p3 → p6) → False) → ((p2 ∧ True) ∨ (True ∨ True))) := by
      intro assump_10
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_9 := assump_1 assump_33
    apply False.elim assump_9
  case inr assump_6 =>
    have assump_34 : (((p3 → p6) → False) → ((p2 ∧ True) ∨ (True ∨ True))) := by
      intro assump_20
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_19 := assump_1 assump_34
    apply False.elim assump_19
  intro assump_26
  have assump_35 : True := by
    apply True.intro
  let assump_29 := assump_26 assump_35
  apply False.elim assump_29


variable (p5 p7 p2 p6 p1 : Prop)
theorem file98_27367 : ((((((p5 ∧ p5) → (p5 ∨ p6)) → False) → (((p7 → p2) → False) ∧ ((p1 → False) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_42 : ((((p5 ∧ p5) → (p5 ∨ p6)) → False) → (((p7 → p2) → False) ∧ ((p1 → False) ∨ (False → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_43 : ((p5 ∧ p5) → (p5 ∨ p6)) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply Or.inl
        exact assump_14
    let assump_11 := assump_5 assump_43
    apply False.elim assump_11
    apply Or.inl
    intro assump_24
    have assump_44 : ((p5 ∧ p5) → (p5 ∨ p6)) := by
      intro assump_29
      cases assump_29
      case intro assump_30 assump_31 =>
        apply Or.inl
        exact assump_31
    let assump_28 := assump_5 assump_44
    apply False.elim assump_28
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p1 p4 p7 p5 p0 : Prop)
theorem file98_28344 : ((((((p0 ∧ p5) → False) ∧ ((p4 ∧ False) ∧ (False → False))) ∧ (((True → True) → (p1 → p5)) ∧ ((False ∧ p1) → False))) ∧ ((((p1 → False) ∧ (p5 → p4)) → ((True ∨ p5) → False)) ∧ (((p7 → False) → False) → False))) → False) := by
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
            apply False.elim assump_13


variable (p5 p2 p7 p0 p4 p6 p1 : Prop)
theorem file98_28989 : (((((p6 ∨ p4) ∧ (p7 ∧ p1)) ∧ ((p1 → False) → (p5 → p0))) ∨ (((True ∨ p7) ∨ (p1 → p1)) ∨ ((p7 ∧ p7) → False))) ∨ ((((True → p2) → False) ∨ ((p5 → False) → False)) → False)) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p3 p5 p0 p1 p6 p4 p7 : Prop)
theorem file98_29324 : (((((p5 → False) → False) → ((p3 ∧ p3) → (p4 ∨ p4))) → (((p4 ∨ True) ∧ (False → p0)) → ((p5 → True) ∨ (p7 → False)))) ∨ ((((True → False) → False) ∧ ((p5 ∧ True) → (p1 → p5))) → (((p5 → p6) ∨ (True ∧ p0)) ∧ ((False ∨ False) ∨ (p1 → False))))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      apply Or.inl
      intro assump_17
      apply True.intro
    case inr assump_10 =>
      apply Or.inl
      intro assump_24
      apply True.intro


variable (p6 p2 p1 p5 p3 p0 : Prop)
theorem file98_29931 : (((((False ∨ p1) ∧ (p2 ∨ p1)) → ((p1 ∧ p0) ∨ (True ∨ p3))) → (((True ∨ p2) → False) → False)) ∨ ((((p1 ∧ p5) ∨ (p2 → True)) ∨ ((p5 → p6) → (p0 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_12 : (True ∨ p2) := by
    apply Or.inl
    apply True.intro
  let assump_8 := assump_2 assump_12
  apply False.elim assump_8


variable (p6 p5 p7 p0 : Prop)
theorem file98_30344 : ((((((p5 ∧ p0) ∧ (p7 ∧ False)) → False) → False) ∧ ((((p0 → p6) → False) → ((False ∨ False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p0 → p6) → False) → ((False ∨ False) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        apply False.elim assump_11
      case inr assump_12 =>
        apply False.elim assump_12
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p1 p5 p6 : Prop)
theorem file98_30927 : ((((((p5 → p5) ∨ (p1 ∧ p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 → p5) ∨ (p1 ∧ p6)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p5 → p5) ∨ (p1 ∧ p6)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p0 p7 p1 p3 p6 p5 : Prop)
theorem file98_31411 : (((((True ∧ p7) ∧ (p5 → p5)) ∨ ((p6 → False) ∨ (True → p4))) → (((p4 ∧ p5) ∨ (p3 ∧ p0)) ∨ ((p3 ∨ p1) → (True ∧ True)))) ∨ ((((p6 → False) → False) → ((p6 ∨ p4) ∨ (p6 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inr
        intro assump_14
        apply And.intro
        apply True.intro
        apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_15 =>
      apply Or.inr
      intro assump_19
      apply And.intro
      apply True.intro
      apply True.intro
    case inr assump_16 =>
      apply Or.inr
      intro assump_22
      apply And.intro
      apply True.intro
      apply True.intro


variable (p2 p1 p7 p6 p3 p0 p4 p5 : Prop)
theorem file98_32287 : (((((p3 ∨ p5) → (p0 → p6)) → ((False ∧ True) → (p4 → p7))) → (((p3 ∨ p5) → (p5 ∨ p2)) ∨ ((p4 ∧ p4) ∧ (p7 → False)))) → ((((False → False) → (p1 → p3)) → ((p6 ∧ False) ∧ (p7 → p6))) → (((p4 ∧ p1) ∨ (False → False)) ∨ ((p2 → True) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inr
  intro assump_7
  apply False.elim assump_7


variable (p5 p6 p1 p4 p2 p0 p3 : Prop)
theorem file98_32706 : (((((False ∨ False) → False) ∨ ((True → False) → (True ∨ p1))) ∨ (((p2 → p1) → (p0 ∧ p4)) ∧ ((p5 → False) → (p2 ∧ False)))) ∨ ((((True → False) ∨ (p1 ∧ p0)) ∨ ((p2 → False) → (p1 ∨ p0))) ∨ (((p6 ∧ p4) → (p3 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply False.elim assump_2
  case inr assump_3 =>
    apply False.elim assump_3


variable (p0 p2 p5 p7 p1 p4 : Prop)
theorem file98_33185 : ((((((p5 → p5) ∧ (p2 ∧ p7)) ∧ ((p0 → p1) → (p2 → False))) ∧ (((p7 → p7) → False) ∧ ((True ∧ False) ∨ (p0 → False)))) ∧ ((((p0 ∧ p4) → (p4 ∧ p0)) ∧ ((p5 → False) → (False → False))) → False)) → False) := by
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
            cases assump_5
            case intro assump_20 assump_21 =>
              cases assump_21
              case inl assump_24 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  apply False.elim assump_27
              case inr assump_25 =>
                have assump_57 : (((p0 ∧ p4) → (p4 ∧ p0)) ∧ ((p5 → False) → (False → False))) := by
                  apply And.intro
                  intro assump_37
                  apply And.intro
                  cases assump_37
                  case intro assump_38 assump_39 =>
                    exact assump_39
                  cases assump_37
                  case intro assump_44 assump_45 =>
                    exact assump_44
                  intro assump_50
                  intro assump_51
                  apply False.elim assump_51
                let assump_36 := assump_3 assump_57
                apply False.elim assump_36


variable (p6 p5 p2 p4 p3 p1 p7 p0 : Prop)
theorem file98_34727 : (((((p5 → False) → False) ∧ ((p0 → p0) → False)) → (((p1 ∨ p1) → (p4 → p5)) ∨ ((p6 ∨ True) → False))) ∨ ((((p2 → p5) → False) ∧ ((p7 → p0) ∨ (p0 ∧ p0))) → (((p0 ∨ True) → (p4 → p2)) → ((False → p6) ∨ (p3 ∨ False))))) := by
  apply Or.inl
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    apply Or.inl
    intro assump_30
    intro assump_31
    cases assump_30
    case inl assump_34 =>
      have assump_58 : (p0 → p0) := by
        intro assump_41
        exact assump_41
      let assump_40 := assump_25 assump_58
      apply False.elim assump_40
    case inr assump_35 =>
      have assump_59 : (p0 → p0) := by
        intro assump_52
        exact assump_52
      let assump_51 := assump_25 assump_59
      apply False.elim assump_51


variable (p2 p5 p6 p1 p7 p0 p4 p3 : Prop)
theorem file98_35558 : (((((p1 ∨ p6) → (p4 → p2)) → ((True → False) → (p4 ∨ p2))) ∨ (((False → p0) → False) ∧ ((p4 → p7) ∨ (p5 ∧ p3)))) ∨ ((((p0 ∧ p3) → (True ∧ p0)) ∨ ((p3 ∧ p2) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_12 : True := by
    apply True.intro
  let assump_8 := assump_2 assump_12
  apply False.elim assump_8


variable (p0 p1 p7 : Prop)
theorem file98_35971 : (((((p7 → False) → (p1 ∧ p0)) → ((False → p1) ∨ (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p7 → False) → (p1 ∧ p0)) → ((False → p1) ∨ (p7 → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p3 p4 : Prop)
theorem file98_36362 : ((((((p4 ∨ p5) → (True ∨ p3)) → False) → False) → False) → False) := by
  intro assump_10
  have assump_31 : ((((p4 ∨ p5) → (True ∨ p3)) → False) → False) := by
    intro assump_14
    have assump_32 : ((p4 ∨ p5) → (True ∨ p3)) := by
      intro assump_18
      cases assump_18
      case inl assump_19 =>
        apply Or.inl
        apply True.intro
      case inr assump_20 =>
        apply Or.inl
        apply True.intro
    let assump_17 := assump_14 assump_32
    apply False.elim assump_17
  let assump_13 := assump_10 assump_31
  apply False.elim assump_13


variable (p4 p5 p0 p3 p7 : Prop)
theorem file98_36985 : (((((p0 ∨ p0) ∧ (p5 ∨ p4)) ∨ ((p5 → p5) → (True ∧ p5))) ∧ (((p0 ∧ p7) ∧ (p5 → False)) ∧ ((p7 → p3) ∧ (False ∨ False)))) → False) := by
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
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case intro assump_20 assump_21 =>
                  cases assump_17
                  case intro assump_28 assump_29 =>
                    cases assump_29
                    case inl assump_32 =>
                      apply False.elim assump_32
                    case inr assump_33 =>
                      apply False.elim assump_33
          case inr assump_13 =>
            cases assump_3
            case intro assump_40 assump_41 =>
              cases assump_40
              case intro assump_42 assump_43 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  cases assump_41
                  case intro assump_52 assump_53 =>
                    cases assump_53
                    case inl assump_56 =>
                      apply False.elim assump_56
                    case inr assump_57 =>
                      apply False.elim assump_57
        case inr assump_9 =>
          cases assump_7
          case inl assump_64 =>
            cases assump_3
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                cases assump_70
                case intro assump_72 assump_73 =>
                  cases assump_69
                  case intro assump_80 assump_81 =>
                    cases assump_81
                    case inl assump_84 =>
                      apply False.elim assump_84
                    case inr assump_85 =>
                      apply False.elim assump_85
          case inr assump_65 =>
            cases assump_3
            case intro assump_92 assump_93 =>
              cases assump_92
              case intro assump_94 assump_95 =>
                cases assump_94
                case intro assump_96 assump_97 =>
                  cases assump_93
                  case intro assump_104 assump_105 =>
                    cases assump_105
                    case inl assump_108 =>
                      apply False.elim assump_108
                    case inr assump_109 =>
                      apply False.elim assump_109
    case inr assump_5 =>
      cases assump_3
      case intro assump_116 assump_117 =>
        cases assump_116
        case intro assump_118 assump_119 =>
          cases assump_118
          case intro assump_120 assump_121 =>
            cases assump_117
            case intro assump_128 assump_129 =>
              cases assump_129
              case inl assump_132 =>
                apply False.elim assump_132
              case inr assump_133 =>
                apply False.elim assump_133


variable (p0 p3 p2 p7 p5 : Prop)
theorem file98_40262 : (((((p7 ∧ p7) → (p7 ∨ p2)) → False) ∧ (((p2 ∧ p5) → (False ∧ p2)) ∨ ((p7 ∨ p3) ∧ (p5 ∨ p0)))) → False) := by
  intro assump_86
  cases assump_86
  case intro assump_87 assump_88 =>
    cases assump_88
    case inl assump_91 =>
      have assump_179 : ((p7 ∧ p7) → (p7 ∨ p2)) := by
        intro assump_97
        cases assump_97
        case intro assump_98 assump_99 =>
          apply Or.inl
          exact assump_99
      let assump_96 := assump_87 assump_179
      apply False.elim assump_96
    case inr assump_92 =>
      cases assump_92
      case intro assump_107 assump_108 =>
        cases assump_107
        case inl assump_109 =>
          cases assump_108
          case inl assump_113 =>
            have assump_180 : ((p7 ∧ p7) → (p7 ∨ p2)) := by
              intro assump_120
              cases assump_120
              case intro assump_121 assump_122 =>
                apply Or.inl
                exact assump_122
            let assump_119 := assump_87 assump_180
            apply False.elim assump_119
          case inr assump_114 =>
            have assump_181 : ((p7 ∧ p7) → (p7 ∨ p2)) := by
              intro assump_135
              cases assump_135
              case intro assump_136 assump_137 =>
                apply Or.inl
                exact assump_137
            let assump_134 := assump_87 assump_181
            apply False.elim assump_134
        case inr assump_110 =>
          cases assump_108
          case inl assump_147 =>
            have assump_182 : ((p7 ∧ p7) → (p7 ∨ p2)) := by
              intro assump_154
              cases assump_154
              case intro assump_155 assump_156 =>
                apply Or.inl
                exact assump_156
            let assump_153 := assump_87 assump_182
            apply False.elim assump_153
          case inr assump_148 =>
            have assump_183 : ((p7 ∧ p7) → (p7 ∨ p2)) := by
              intro assump_169
              cases assump_169
              case intro assump_170 assump_171 =>
                apply Or.inl
                exact assump_171
            let assump_168 := assump_87 assump_183
            apply False.elim assump_168


variable (p7 p0 : Prop)
theorem file98_42470 : ((((((p7 ∧ p0) → (False → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p7 ∧ p0) → (False → False)) → False) → False) := by
    intro assump_5
    have assump_20 : ((p7 ∧ p0) → (False → False)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_20
    apply False.elim assump_8
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p7 p1 p6 p0 p5 p3 : Prop)
theorem file98_42987 : (((((p0 ∧ p5) ∨ (p6 → p1)) ∧ ((p0 ∨ p5) ∧ (False ∧ p7))) → (((False → False) ∨ (p5 → p5)) → False)) ∨ ((((False → p4) ∧ (False ∨ p6)) ∧ ((p4 ∨ p7) ∨ (p3 → False))) ∨ (((p0 → False) → False) → ((p0 → False) → (p3 ∨ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_8
          case intro assump_17 assump_18 =>
            cases assump_17
            case inl assump_19 =>
              cases assump_18
              case intro assump_23 assump_24 =>
                apply False.elim assump_23
            case inr assump_20 =>
              cases assump_18
              case intro assump_29 assump_30 =>
                apply False.elim assump_29
      case inr assump_10 =>
        cases assump_8
        case intro assump_35 assump_36 =>
          cases assump_35
          case inl assump_37 =>
            cases assump_36
            case intro assump_41 assump_42 =>
              apply False.elim assump_41
          case inr assump_38 =>
            cases assump_36
            case intro assump_47 assump_48 =>
              apply False.elim assump_47
  case inr assump_4 =>
    cases assump_1
    case intro assump_53 assump_54 =>
      cases assump_53
      case inl assump_55 =>
        cases assump_55
        case intro assump_57 assump_58 =>
          cases assump_54
          case intro assump_63 assump_64 =>
            cases assump_63
            case inl assump_65 =>
              cases assump_64
              case intro assump_69 assump_70 =>
                apply False.elim assump_69
            case inr assump_66 =>
              cases assump_64
              case intro assump_75 assump_76 =>
                apply False.elim assump_75
      case inr assump_56 =>
        cases assump_54
        case intro assump_81 assump_82 =>
          cases assump_81
          case inl assump_83 =>
            cases assump_82
            case intro assump_87 assump_88 =>
              apply False.elim assump_87
          case inr assump_84 =>
            cases assump_82
            case intro assump_93 assump_94 =>
              apply False.elim assump_93


variable (p7 p4 p1 p3 p5 : Prop)
theorem file98_45370 : ((((((False ∨ p7) → False) → False) → (((p4 ∧ p1) ∧ (False ∧ p3)) → ((p7 ∧ False) ∨ (p5 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False ∨ p7) → False) → False) → (((p4 ∧ p1) ∧ (False ∧ p3)) → ((p7 ∧ False) ∨ (p5 ∧ p4)))) := by
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


variable (p7 p2 p1 p0 p3 p4 p6 p5 : Prop)
theorem file98_46014 : ((((((p2 → True) ∧ (p4 → False)) ∨ ((p6 → False) ∧ (p5 → p2))) ∧ (((False ∧ p3) → False) ∨ ((p5 ∨ p1) ∧ (False ∨ p4)))) ∧ ((((p0 ∧ p0) → (p7 ∨ p1)) → False) ∧ (((False ∧ p3) → False) → False))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_18
      case inl assump_20 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          cases assump_19
          case inl assump_28 =>
            cases assump_17
            case intro assump_32 assump_33 =>
              have assump_172 : ((False ∧ p3) → False) := by
                intro assump_39
                cases assump_39
                case intro assump_40 assump_41 =>
                  apply False.elim assump_40
              let assump_38 := assump_33 assump_172
              apply False.elim assump_38
          case inr assump_29 =>
            cases assump_29
            case intro assump_47 assump_48 =>
              cases assump_47
              case inl assump_49 =>
                cases assump_48
                case inl assump_53 =>
                  apply False.elim assump_53
                case inr assump_54 =>
                  cases assump_17
                  case intro assump_59 assump_60 =>
                    have assump_173 : ((False ∧ p3) → False) := by
                      intro assump_66
                      cases assump_66
                      case intro assump_67 assump_68 =>
                        apply False.elim assump_67
                    let assump_65 := assump_60 assump_173
                    apply False.elim assump_65
              case inr assump_50 =>
                cases assump_48
                case inl assump_76 =>
                  apply False.elim assump_76
                case inr assump_77 =>
                  cases assump_17
                  case intro assump_82 assump_83 =>
                    have assump_174 : ((False ∧ p3) → False) := by
                      intro assump_89
                      cases assump_89
                      case intro assump_90 assump_91 =>
                        apply False.elim assump_90
                    let assump_88 := assump_83 assump_174
                    apply False.elim assump_88
      case inr assump_21 =>
        cases assump_21
        case intro assump_97 assump_98 =>
          cases assump_19
          case inl assump_103 =>
            cases assump_17
            case intro assump_107 assump_108 =>
              have assump_175 : ((False ∧ p3) → False) := by
                intro assump_114
                cases assump_114
                case intro assump_115 assump_116 =>
                  apply False.elim assump_115
              let assump_113 := assump_108 assump_175
              apply False.elim assump_113
          case inr assump_104 =>
            cases assump_104
            case intro assump_122 assump_123 =>
              cases assump_122
              case inl assump_124 =>
                cases assump_123
                case inl assump_128 =>
                  apply False.elim assump_128
                case inr assump_129 =>
                  cases assump_17
                  case intro assump_134 assump_135 =>
                    have assump_176 : ((False ∧ p3) → False) := by
                      intro assump_141
                      cases assump_141
                      case intro assump_142 assump_143 =>
                        apply False.elim assump_142
                    let assump_140 := assump_135 assump_176
                    apply False.elim assump_140
              case inr assump_125 =>
                cases assump_123
                case inl assump_151 =>
                  apply False.elim assump_151
                case inr assump_152 =>
                  cases assump_17
                  case intro assump_157 assump_158 =>
                    have assump_177 : ((False ∧ p3) → False) := by
                      intro assump_164
                      cases assump_164
                      case intro assump_165 assump_166 =>
                        apply False.elim assump_165
                    let assump_163 := assump_158 assump_177
                    apply False.elim assump_163


variable (p7 p2 p6 p1 p0 p4 : Prop)
theorem file98_50351 : (((((p1 → False) ∧ (p1 ∧ False)) → False) ∨ (((p4 ∧ p7) → (p1 → False)) → False)) ∨ ((((p6 ∨ p1) → (True → p0)) → ((True ∨ True) ∨ (p0 ∧ p1))) → (((p1 ∧ False) ∨ (p2 → False)) → ((p4 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      apply False.elim assump_11


variable (p3 p5 p0 p1 p6 : Prop)
theorem file98_50806 : (((((p1 → p1) → False) ∧ ((p5 ∧ p3) → (p5 → False))) → False) ∨ ((((p0 → False) → (p1 ∨ p3)) → False) → (((p0 ∧ p6) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (p1 → p1) := by
      intro assump_10
      exact assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p3 p0 p1 p4 p5 p7 p2 p6 : Prop)
theorem file98_51247 : (((((p4 → True) ∨ (False ∧ p2)) ∨ ((p5 → p1) ∧ (True → False))) ∨ (((p5 ∧ p3) → False) ∧ ((p3 ∧ False) ∨ (p2 ∧ p0)))) ∨ ((((p0 ∧ p7) → (p2 → p6)) → False) → (((p5 ∨ False) → False) → ((p6 → p2) ∧ (p4 → True))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply True.intro


variable (p7 p1 p3 p0 p6 p2 : Prop)
theorem file98_51621 : (((((p1 ∨ p3) ∧ (p7 ∧ p3)) → ((p7 → False) → False)) ∨ (((p6 ∨ p2) → (p6 → False)) → ((p1 → p0) → False))) ∨ ((((p6 ∨ True) ∧ (p2 ∨ False)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        have assump_39 : p7 := by
          exact assump_11
        let assump_20 := assump_2 assump_39
        apply False.elim assump_20
    case inr assump_8 =>
      cases assump_6
      case intro assump_26 assump_27 =>
        have assump_40 : p7 := by
          exact assump_26
        let assump_35 := assump_2 assump_40
        apply False.elim assump_35


variable (p2 p5 p7 p1 p6 p4 p3 p0 : Prop)
theorem file98_52436 : (((((p0 → False) → (p0 → p1)) ∨ ((p2 ∧ p7) → False)) ∧ (((p3 ∨ p6) → False) ∨ ((p4 → False) → (False ∨ p1)))) → ((((p0 → p0) → False) → ((False ∨ False) → (True → p0))) ∨ (((p5 → False) → (True ∧ False)) ∧ ((p0 → p7) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        intro assump_14
        cases assump_13
        case inl assump_17 =>
          apply False.elim assump_17
        case inr assump_18 =>
          apply False.elim assump_18
      case inr assump_9 =>
        apply Or.inl
        intro assump_25
        intro assump_26
        intro assump_27
        cases assump_26
        case inl assump_30 =>
          apply False.elim assump_30
        case inr assump_31 =>
          apply False.elim assump_31
    case inr assump_5 =>
      cases assump_3
      case inl assump_38 =>
        apply Or.inl
        intro assump_42
        intro assump_43
        intro assump_44
        cases assump_43
        case inl assump_47 =>
          apply False.elim assump_47
        case inr assump_48 =>
          apply False.elim assump_48
      case inr assump_39 =>
        apply Or.inl
        intro assump_55
        intro assump_56
        intro assump_57
        cases assump_56
        case inl assump_60 =>
          apply False.elim assump_60
        case inr assump_61 =>
          apply False.elim assump_61


variable (p7 p5 p6 p4 p0 p3 p1 : Prop)
theorem file98_54027 : (((((p4 → False) ∧ (p6 ∧ False)) → False) ∨ (((p3 → p1) → False) ∧ ((False → p6) ∧ (p5 ∨ p6)))) → ((((False ∧ p0) → (False ∨ p7)) ∨ ((p3 ∨ p0) ∧ (p1 ∧ True))) ∨ (((False ∧ True) ∧ (False ∨ p6)) → ((False ∧ p3) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  case inr assump_3 =>
    cases assump_3
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        cases assump_16
        case inl assump_19 =>
          apply Or.inl
          apply Or.inl
          intro assump_23
          cases assump_23
          case intro assump_24 assump_25 =>
            apply False.elim assump_24
        case inr assump_20 =>
          apply Or.inl
          apply Or.inl
          intro assump_30
          cases assump_30
          case intro assump_31 assump_32 =>
            apply False.elim assump_31


variable (p0 p1 p5 p4 : Prop)
theorem file98_55094 : ((((((p1 → p0) → False) → False) ∨ (((False → False) → False) ∨ ((p4 ∨ p1) ∧ (p0 → True)))) ∧ ((((False ∨ p5) → (False → p0)) → ((True ∨ p5) ∧ (p4 ∨ True))) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      have assump_74 : (((False ∨ p5) → (False → p0)) → ((True ∨ p5) ∧ (p4 ∨ True))) := by
        intro assump_17
        apply And.intro
        apply Or.inl
        apply True.intro
        apply Or.inr
        apply True.intro
      let assump_16 := assump_9 assump_74
      apply False.elim assump_16
    case inr assump_11 =>
      cases assump_11
      case inl assump_25 =>
        have assump_75 : (((False ∨ p5) → (False → p0)) → ((True ∨ p5) ∧ (p4 ∨ True))) := by
          intro assump_32
          apply And.intro
          apply Or.inl
          apply True.intro
          apply Or.inr
          apply True.intro
        let assump_31 := assump_9 assump_75
        apply False.elim assump_31
      case inr assump_26 =>
        cases assump_26
        case intro assump_40 assump_41 =>
          cases assump_40
          case inl assump_42 =>
            have assump_76 : (((False ∨ p5) → (False → p0)) → ((True ∨ p5) ∧ (p4 ∨ True))) := by
              intro assump_51
              apply And.intro
              apply Or.inl
              apply True.intro
              apply Or.inl
              exact assump_42
            let assump_50 := assump_9 assump_76
            apply False.elim assump_50
          case inr assump_43 =>
            have assump_77 : (((False ∨ p5) → (False → p0)) → ((True ∨ p5) ∧ (p4 ∨ True))) := by
              intro assump_66
              apply And.intro
              apply Or.inl
              apply True.intro
              apply Or.inr
              apply True.intro
            let assump_65 := assump_9 assump_77
            apply False.elim assump_65


variable (p0 p4 p7 p6 p3 p2 p5 p1 : Prop)
theorem file98_57064 : ((((((p7 ∨ p5) → (True ∧ p5)) → ((p7 → False) → (True ∨ p4))) → False) ∧ ((((p7 ∨ p1) ∧ (p2 → True)) → False) ∧ (((True ∧ p0) ∨ (p6 → False)) ∨ ((p0 ∨ p6) ∧ (p3 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_84 : (((p7 ∨ p5) → (True ∧ p5)) → ((p7 → False) → (True ∨ p4))) := by
              intro assump_23
              intro assump_24
              apply Or.inl
              apply True.intro
            let assump_22 := assump_2 assump_84
            apply False.elim assump_22
        case inr assump_13 =>
          have assump_85 : (((p7 ∨ p5) → (True ∧ p5)) → ((p7 → False) → (True ∨ p4))) := by
            intro assump_37
            intro assump_38
            apply Or.inl
            apply True.intro
          let assump_36 := assump_2 assump_85
          apply False.elim assump_36
      case inr assump_11 =>
        cases assump_11
        case intro assump_46 assump_47 =>
          cases assump_46
          case inl assump_48 =>
            have assump_86 : (((p7 ∨ p5) → (True ∧ p5)) → ((p7 → False) → (True ∨ p4))) := by
              intro assump_58
              intro assump_59
              apply Or.inl
              apply True.intro
            let assump_57 := assump_2 assump_86
            apply False.elim assump_57
          case inr assump_49 =>
            have assump_87 : (((p7 ∨ p5) → (True ∧ p5)) → ((p7 → False) → (True ∨ p4))) := by
              intro assump_75
              intro assump_76
              apply Or.inl
              apply True.intro
            let assump_74 := assump_2 assump_87
            apply False.elim assump_74


variable (p2 p4 p1 p7 p0 p5 p3 : Prop)
theorem file98_59008 : (((((True → True) ∧ (p2 ∧ False)) → False) → False) → ((((p2 → p0) ∧ (p3 → p4)) → ((True → False) ∨ (p5 → False))) ∧ (((p5 → False) ∨ (p7 ∨ p1)) ∧ ((p5 → p1) ∨ (True → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    intro assump_11
    have assump_71 : (((True → True) ∧ (p2 ∧ False)) → False) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
    let assump_14 := assump_1 assump_71
    apply False.elim assump_14
  apply And.intro
  apply Or.inl
  intro assump_31
  have assump_72 : (((True → True) ∧ (p2 ∧ False)) → False) := by
    intro assump_36
    cases assump_36
    case intro assump_37 assump_38 =>
      cases assump_38
      case intro assump_41 assump_42 =>
        apply False.elim assump_42
  let assump_35 := assump_1 assump_72
  apply False.elim assump_35
  apply Or.inl
  intro assump_52
  have assump_73 : (((True → True) ∧ (p2 ∧ False)) → False) := by
    intro assump_57
    cases assump_57
    case intro assump_58 assump_59 =>
      cases assump_59
      case intro assump_62 assump_63 =>
        apply False.elim assump_63
  let assump_56 := assump_1 assump_73
  apply False.elim assump_56


variable (p1 p0 p3 : Prop)
theorem file98_60410 : ((((((p0 → False) ∨ (p1 → False)) → False) → False) ∧ ((((True ∨ p3) → False) → False) → False)) → False) := by
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    have assump_26 : (((True ∨ p3) → False) → False) := by
      intro assump_16
      have assump_27 : (True ∨ p3) := by
        apply Or.inl
        apply True.intro
      let assump_19 := assump_16 assump_27
      apply False.elim assump_19
    let assump_15 := assump_10 assump_26
    apply False.elim assump_15


variable (p4 p7 p2 p3 p5 p0 p6 : Prop)
theorem file98_60970 : (((((True → False) ∨ (False ∧ p3)) → ((True ∧ False) → (p4 ∨ p0))) → False) → ((((p3 ∨ p4) → (p3 → p5)) → False) → (((p7 → p6) ∧ (p2 ∨ True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      have assump_46 : (((True → False) ∨ (False ∧ p3)) → ((True ∧ False) → (p4 ∨ p0))) := by
        intro assump_17
        intro assump_18
        cases assump_18
        case intro assump_19 assump_20 =>
          apply False.elim assump_20
      let assump_16 := assump_1 assump_46
      apply False.elim assump_16
    case inr assump_9 =>
      have assump_47 : (((True → False) ∨ (False ∧ p3)) → ((True ∧ False) → (p4 ∨ p0))) := by
        intro assump_35
        intro assump_36
        cases assump_36
        case intro assump_37 assump_38 =>
          apply False.elim assump_38
      let assump_34 := assump_1 assump_47
      apply False.elim assump_34


variable (p5 p1 p3 p2 p4 p7 p0 p6 : Prop)
theorem file98_62006 : ((((((p7 → False) ∧ (False ∨ p0)) ∧ ((p3 ∧ p2) → (p4 → p3))) → (((p1 → False) ∧ (False → False)) ∧ ((p3 → False) → (p7 → False)))) ∧ ((((p0 ∨ p7) ∨ (p3 → True)) → False) ∧ (((p3 ∧ p6) ∨ (p5 ∧ p5)) ∨ ((p6 → False) ∧ (p7 ∧ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_56 : ((p0 ∨ p7) ∨ (p3 → True)) := by
              apply Or.inr
              intro assump_23
              apply True.intro
            let assump_22 := assump_6 assump_56
            apply False.elim assump_22
        case inr assump_13 =>
          cases assump_13
          case intro assump_27 assump_28 =>
            have assump_57 : ((p0 ∨ p7) ∨ (p3 → True)) := by
              apply Or.inr
              intro assump_36
              apply True.intro
            let assump_35 := assump_6 assump_57
            apply False.elim assump_35
      case inr assump_11 =>
        cases assump_11
        case intro assump_40 assump_41 =>
          cases assump_41
          case intro assump_44 assump_45 =>
            have assump_58 : ((p0 ∨ p7) ∨ (p3 → True)) := by
              apply Or.inl
              apply Or.inr
              exact assump_44
            let assump_52 := assump_6 assump_58
            apply False.elim assump_52


variable (p5 p0 p6 p1 p3 p7 p4 : Prop)
theorem file98_63579 : (((((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) → False) → ((((p7 → p5) → False) ∨ ((p3 ∧ True) ∧ (True ∧ p0))) → (((p7 ∧ p5) ∨ (p5 → False)) → ((p6 ∧ p3) ∧ (p0 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply And.intro
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case inl assump_12 =>
        have assump_339 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
          intro assump_19
          cases assump_19
          case inl assump_20 =>
            apply Or.inr
            intro assump_24
            exact assump_24
          case inr assump_21 =>
            apply Or.inr
            intro assump_29
            exact assump_29
        let assump_18 := assump_1 assump_339
        apply False.elim assump_18
      case inr assump_13 =>
        cases assump_13
        case intro assump_35 assump_36 =>
          cases assump_35
          case intro assump_37 assump_38 =>
            cases assump_36
            case intro assump_43 assump_44 =>
              have assump_340 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
                intro assump_52
                cases assump_52
                case inl assump_53 =>
                  apply Or.inr
                  intro assump_57
                  exact assump_57
                case inr assump_54 =>
                  apply Or.inr
                  intro assump_62
                  exact assump_62
              let assump_51 := assump_1 assump_340
              apply False.elim assump_51
  case inr assump_5 =>
    cases assump_2
    case inl assump_70 =>
      have assump_341 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
        intro assump_77
        cases assump_77
        case inl assump_78 =>
          apply Or.inr
          intro assump_82
          exact assump_82
        case inr assump_79 =>
          apply Or.inr
          intro assump_87
          exact assump_87
      let assump_76 := assump_1 assump_341
      apply False.elim assump_76
    case inr assump_71 =>
      cases assump_71
      case intro assump_93 assump_94 =>
        cases assump_93
        case intro assump_95 assump_96 =>
          cases assump_94
          case intro assump_101 assump_102 =>
            have assump_342 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
              intro assump_110
              cases assump_110
              case inl assump_111 =>
                apply Or.inr
                intro assump_115
                exact assump_115
              case inr assump_112 =>
                apply Or.inr
                intro assump_120
                exact assump_120
            let assump_109 := assump_1 assump_342
            apply False.elim assump_109
  cases assump_3
  case inl assump_126 =>
    cases assump_126
    case intro assump_128 assump_129 =>
      cases assump_2
      case inl assump_134 =>
        have assump_343 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
          intro assump_141
          cases assump_141
          case inl assump_142 =>
            apply Or.inr
            intro assump_146
            exact assump_146
          case inr assump_143 =>
            apply Or.inr
            intro assump_151
            exact assump_151
        let assump_140 := assump_1 assump_343
        apply False.elim assump_140
      case inr assump_135 =>
        cases assump_135
        case intro assump_157 assump_158 =>
          cases assump_157
          case intro assump_159 assump_160 =>
            cases assump_158
            case intro assump_165 assump_166 =>
              exact assump_159
  case inr assump_127 =>
    cases assump_2
    case inl assump_175 =>
      have assump_344 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
        intro assump_182
        cases assump_182
        case inl assump_183 =>
          apply Or.inr
          intro assump_187
          exact assump_187
        case inr assump_184 =>
          apply Or.inr
          intro assump_192
          exact assump_192
      let assump_181 := assump_1 assump_344
      apply False.elim assump_181
    case inr assump_176 =>
      cases assump_176
      case intro assump_198 assump_199 =>
        cases assump_198
        case intro assump_200 assump_201 =>
          cases assump_199
          case intro assump_206 assump_207 =>
            exact assump_200
  intro assump_214
  cases assump_3
  case inl assump_217 =>
    cases assump_217
    case intro assump_219 assump_220 =>
      cases assump_2
      case inl assump_225 =>
        have assump_345 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
          intro assump_232
          cases assump_232
          case inl assump_233 =>
            apply Or.inr
            intro assump_237
            exact assump_237
          case inr assump_234 =>
            apply Or.inr
            intro assump_242
            exact assump_242
        let assump_231 := assump_1 assump_345
        apply False.elim assump_231
      case inr assump_226 =>
        cases assump_226
        case intro assump_248 assump_249 =>
          cases assump_248
          case intro assump_250 assump_251 =>
            cases assump_249
            case intro assump_256 assump_257 =>
              have assump_346 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
                intro assump_265
                cases assump_265
                case inl assump_266 =>
                  apply Or.inr
                  intro assump_270
                  exact assump_270
                case inr assump_267 =>
                  apply Or.inr
                  intro assump_275
                  exact assump_275
              let assump_264 := assump_1 assump_346
              apply False.elim assump_264
  case inr assump_218 =>
    cases assump_2
    case inl assump_283 =>
      have assump_347 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
        intro assump_290
        cases assump_290
        case inl assump_291 =>
          apply Or.inr
          intro assump_295
          exact assump_295
        case inr assump_292 =>
          apply Or.inr
          intro assump_300
          exact assump_300
      let assump_289 := assump_1 assump_347
      apply False.elim assump_289
    case inr assump_284 =>
      cases assump_284
      case intro assump_306 assump_307 =>
        cases assump_306
        case intro assump_308 assump_309 =>
          cases assump_307
          case intro assump_314 assump_315 =>
            have assump_348 : (((False → False) ∨ (p4 → True)) → ((p1 ∧ False) ∨ (p7 → p7))) := by
              intro assump_323
              cases assump_323
              case inl assump_324 =>
                apply Or.inr
                intro assump_328
                exact assump_328
              case inr assump_325 =>
                apply Or.inr
                intro assump_333
                exact assump_333
            let assump_322 := assump_1 assump_348
            apply False.elim assump_322


variable (p2 p0 p3 p6 p5 : Prop)
theorem file98_70869 : (((((False → False) ∨ (p2 → p0)) → ((p5 ∨ p2) ∧ (p3 ∧ False))) ∧ (((p6 → True) ∨ (False → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((p6 → True) ∨ (False → False)) := by
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p6 p1 p3 p5 p0 : Prop)
theorem file98_71308 : ((((((p5 ∧ False) ∧ (p3 ∧ p6)) → False) ∨ (((True → False) ∨ (p0 ∨ p1)) → ((p1 → False) ∨ (p1 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p5 ∧ False) ∧ (p3 ∧ p6)) → False) ∨ (((True → False) ∨ (p0 ∨ p1)) → ((p1 → False) ∨ (p1 ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p3 p5 : Prop)
theorem file98_71875 : (((((False → False) → False) → ((p3 → p3) ∨ (False → p5))) → False) → False) := by
  intro assump_4
  have assump_17 : (((False → False) → False) → ((p3 → p3) ∨ (False → p5))) := by
    intro assump_8
    apply Or.inl
    intro assump_11
    exact assump_11
  let assump_7 := assump_4 assump_17
  apply False.elim assump_7


variable (p6 p3 p0 p4 p7 p5 p1 p2 : Prop)
theorem file98_72264 : (((((p5 → False) ∧ (True → p4)) → ((p4 ∧ p2) → False)) → False) → ((((p1 → p5) ∧ (p1 ∨ p4)) ∧ ((p0 ∧ p0) ∨ (p1 ∨ p2))) → (((p0 → p7) → (p3 → True)) ∨ ((p2 ∨ p6) ∨ (p6 ∨ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        cases assump_4
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            apply Or.inl
            intro assump_23
            intro assump_24
            apply True.intro
        case inr assump_14 =>
          cases assump_14
          case inl assump_25 =>
            apply Or.inl
            intro assump_31
            intro assump_32
            apply True.intro
          case inr assump_26 =>
            apply Or.inl
            intro assump_37
            intro assump_38
            apply True.intro
      case inr assump_10 =>
        cases assump_4
        case inl assump_41 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            apply Or.inl
            intro assump_51
            intro assump_52
            apply True.intro
        case inr assump_42 =>
          cases assump_42
          case inl assump_53 =>
            apply Or.inl
            intro assump_59
            intro assump_60
            apply True.intro
          case inr assump_54 =>
            apply Or.inl
            intro assump_65
            intro assump_66
            apply True.intro


variable (p2 p5 p1 p3 p7 p0 p4 p6 : Prop)
theorem file98_73878 : (((((p7 → False) ∧ (False ∧ p0)) → False) ∨ (((p0 → False) ∨ (p1 ∧ p7)) ∧ ((p5 → True) ∨ (p4 → False)))) ∧ ((((p0 ∨ p2) → False) → False) → (((p6 ∨ p4) ∧ (p5 → p3)) ∨ ((p6 → True) → (True ∨ p2))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  intro assump_10
  apply Or.inr
  intro assump_13
  apply Or.inl
  apply True.intro


variable (p6 p5 p1 p7 p0 p3 p4 : Prop)
theorem file98_74418 : (((((False → False) → False) ∧ ((False ∧ False) → False)) → (((True → p3) → (p0 ∨ False)) ∨ ((p0 ∨ p5) → (p3 → False)))) ∨ ((((p4 ∧ p4) ∧ (True → False)) ∧ ((p3 → p5) → (p6 → p6))) ∧ (((p7 ∧ True) → (p0 ∧ p1)) → ((True → False) ∨ (p3 → p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    have assump_21 : (False → False) := by
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_2 assump_21
    apply False.elim assump_14


variable (p5 p3 p1 p2 : Prop)
theorem file98_75010 : ((((((True ∨ p5) → False) ∧ ((p2 ∨ p3) ∨ (False ∨ p1))) → False) → False) → False) := by
  intro assump_1
  have assump_42 : ((((True ∨ p5) → False) ∧ ((p2 ∨ p3) ∨ (False ∨ p1))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          have assump_43 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_17 := assump_6 assump_43
          apply False.elim assump_17
        case inr assump_13 =>
          have assump_44 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_24 := assump_6 assump_44
          apply False.elim assump_24
      case inr assump_11 =>
        cases assump_11
        case inl assump_28 =>
          apply False.elim assump_28
        case inr assump_29 =>
          have assump_45 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_35 := assump_6 assump_45
          apply False.elim assump_35
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p0 p7 p2 p4 p1 p6 : Prop)
theorem file98_76231 : ((((((True → p4) → False) → ((p4 → False) ∨ (p4 ∧ False))) → False) ∧ ((((p0 ∧ p2) ∨ (p6 ∨ True)) → ((p1 ∧ p1) ∧ (p1 → False))) ∧ (((p7 ∧ p1) ∧ (p2 → False)) ∨ ((False → p1) ∧ (False → False))))) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_20
    case intro assump_23 assump_24 =>
      cases assump_24
      case inl assump_27 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            have assump_83 : ((p0 ∧ p2) ∨ (p6 ∨ True)) := by
              apply Or.inr
              apply Or.inr
              apply True.intro
            let assump_42 := assump_23 assump_83
            let assump_43 := And.right assump_42
            have assump_84 : p1 := by
              exact assump_32
            let assump_47 := assump_43 assump_84
            apply False.elim assump_47
      case inr assump_28 =>
        cases assump_28
        case intro assump_51 assump_52 =>
          have assump_85 : (((True → p4) → False) → ((p4 → False) ∨ (p4 ∧ False))) := by
            intro assump_66
            apply Or.inl
            intro assump_69
            have assump_86 : (True → p4) := by
              intro assump_74
              exact assump_69
            let assump_73 := assump_66 assump_86
            apply False.elim assump_73
          let assump_65 := assump_19 assump_85
          apply False.elim assump_65


variable (p3 p7 p1 p2 p0 p4 p5 p6 : Prop)
theorem file98_77767 : ((((((False → False) ∧ (p3 → p6)) → ((p6 → False) ∨ (p5 ∧ p4))) → (((p6 ∨ False) ∨ (p6 ∨ False)) ∨ ((p0 ∨ p0) ∧ (p6 → False)))) ∧ ((((False → p6) ∨ (p4 → False)) → False) ∧ (((p2 ∨ p7) ∧ (p7 ∨ p3)) ∨ ((p1 → False) ∧ (p1 ∨ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case inl assump_18 =>
              have assump_83 : ((False → p6) ∨ (p4 → False)) := by
                apply Or.inl
                intro assump_25
                apply False.elim assump_25
              let assump_24 := assump_6 assump_83
              apply False.elim assump_24
            case inr assump_19 =>
              have assump_84 : ((False → p6) ∨ (p4 → False)) := by
                apply Or.inl
                intro assump_36
                apply False.elim assump_36
              let assump_35 := assump_6 assump_84
              apply False.elim assump_35
          case inr assump_15 =>
            cases assump_13
            case inl assump_44 =>
              have assump_85 : ((False → p6) ∨ (p4 → False)) := by
                apply Or.inl
                intro assump_51
                apply False.elim assump_51
              let assump_50 := assump_6 assump_85
              apply False.elim assump_50
            case inr assump_45 =>
              have assump_86 : ((False → p6) ∨ (p4 → False)) := by
                apply Or.inl
                intro assump_62
                apply False.elim assump_62
              let assump_61 := assump_6 assump_86
              apply False.elim assump_61
      case inr assump_11 =>
        cases assump_11
        case intro assump_68 assump_69 =>
          cases assump_69
          case inl assump_72 =>
            have assump_87 : p1 := by
              exact assump_72
            let assump_77 := assump_68 assump_87
            apply False.elim assump_77
          case inr assump_73 =>
            apply False.elim assump_73


variable (p4 p7 p5 p6 p0 p1 p3 : Prop)
theorem file98_80025 : (((((True ∨ p5) → (p0 ∧ False)) ∧ ((p3 ∨ p1) ∧ (p3 → False))) → (((p6 → False) ∧ (p5 → False)) ∨ ((p6 → True) → (False → False)))) ∨ ((((p3 ∧ p4) → False) ∨ ((p5 → p5) ∨ (p5 → False))) ∧ (((p7 → False) → False) ∧ ((p4 ∨ p3) → (p7 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        apply And.intro
        intro assump_14
        have assump_58 : p3 := by
          exact assump_8
        let assump_18 := assump_7 assump_58
        apply False.elim assump_18
        intro assump_22
        have assump_59 : p3 := by
          exact assump_8
        let assump_26 := assump_7 assump_59
        apply False.elim assump_26
      case inr assump_9 =>
        apply Or.inl
        apply And.intro
        intro assump_34
        have assump_60 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_40 := assump_2 assump_60
        let assump_41 := And.right assump_40
        apply False.elim assump_41
        intro assump_46
        have assump_61 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_52 := assump_2 assump_61
        let assump_53 := And.right assump_52
        apply False.elim assump_53


variable (p3 p0 p1 p6 p7 p5 p2 : Prop)
theorem file98_81445 : (((((p1 → p6) → (False → False)) → False) → (((p0 → p2) → (p2 ∧ p2)) ∧ ((p2 ∧ p6) ∨ (True ∨ False)))) ∨ ((((p5 ∧ p2) → (p2 ∧ p1)) → False) ∧ (((p0 ∨ False) ∨ (False → False)) → ((p7 → False) ∧ (p3 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  have assump_29 : ((p1 → p6) → (False → False)) := by
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_7 := assump_1 assump_29
  apply False.elim assump_7
  have assump_30 : ((p1 → p6) → (False → False)) := by
    intro assump_20
    intro assump_21
    apply False.elim assump_21
  let assump_19 := assump_1 assump_30
  apply False.elim assump_19
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p7 p2 p0 p5 p4 p3 p6 : Prop)
theorem file98_82236 : (((((p5 ∨ p0) → (p3 → False)) ∧ ((p5 → False) → False)) ∧ (((True → False) ∧ (p6 → p5)) ∧ ((p7 → p0) ∨ (p0 → False)))) → ((((True ∨ p5) → (True → p0)) ∨ ((p0 ∧ p7) → False)) → (((p6 ∧ p2) ∨ (p4 → p0)) ∨ ((p6 ∧ p0) ∧ (p4 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_16
            case inl assump_23 =>
              apply Or.inl
              apply Or.inr
              intro assump_27
              have assump_93 : True := by
                apply True.intro
              let assump_33 := assump_17 assump_93
              apply False.elim assump_33
            case inr assump_24 =>
              apply Or.inl
              apply Or.inr
              intro assump_39
              have assump_94 : True := by
                apply True.intro
              let assump_45 := assump_17 assump_94
              apply False.elim assump_45
  case inr assump_4 =>
    cases assump_1
    case intro assump_51 assump_52 =>
      cases assump_51
      case intro assump_53 assump_54 =>
        cases assump_52
        case intro assump_59 assump_60 =>
          cases assump_59
          case intro assump_61 assump_62 =>
            cases assump_60
            case inl assump_67 =>
              apply Or.inl
              apply Or.inr
              intro assump_71
              have assump_95 : True := by
                apply True.intro
              let assump_77 := assump_61 assump_95
              apply False.elim assump_77
            case inr assump_68 =>
              apply Or.inl
              apply Or.inr
              intro assump_83
              have assump_96 : True := by
                apply True.intro
              let assump_89 := assump_61 assump_96
              apply False.elim assump_89


variable (p0 p7 p6 p4 p2 p5 : Prop)
theorem file98_84333 : ((((((p2 → p7) → False) → False) → False) ∧ ((((p5 ∧ p4) → (p0 → p6)) → False) ∧ (((True → False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_23 : ((True → False) → False) := by
        intro assump_13
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_13 assump_24
        apply False.elim assump_16
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12


variable (p3 p5 p4 p1 : Prop)
theorem file98_84939 : (((((p5 ∧ False) → False) → False) → False) ∨ ((((p4 → False) ∨ (p5 → p3)) → False) ∨ (((p1 → False) ∧ (p1 ∧ p1)) → ((False → False) ∨ (p4 ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p5 ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p4 p3 p5 p7 p2 : Prop)
theorem file98_85405 : ((((((True ∨ p4) → False) → ((False ∧ p2) → False)) ∨ (((p7 ∧ p6) ∨ (p2 → False)) ∧ ((p4 → False) ∨ (p3 → False)))) → ((((p7 ∧ False) ∧ (p6 ∧ p5)) → False) → False)) → False) := by
  intro assump_1
  have assump_24 : ((((True ∨ p4) → False) → ((False ∧ p2) → False)) ∨ (((p7 ∧ p6) ∨ (p2 → False)) ∧ ((p4 → False) ∨ (p3 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_24
  have assump_25 : (((p7 ∧ False) ∧ (p6 ∧ p5)) → False) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
  let assump_11 := assump_4 assump_25
  apply False.elim assump_11


variable (p2 p7 p4 p6 p1 p3 p0 : Prop)
theorem file98_86288 : (((((p0 ∨ False) ∧ (p0 ∧ p3)) → ((p1 → p3) → (p0 ∨ p4))) ∨ (((p4 ∨ p0) → (True ∧ p4)) → ((p6 ∧ p1) → (p2 ∨ p2)))) ∨ ((((p1 → p2) → False) ∧ ((p0 → False) → (p0 → False))) ∧ (((True ∧ True) → False) ∨ ((p6 ∨ p1) ∨ (p7 ∧ p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        apply Or.inl
        exact assump_11
    case inr assump_8 =>
      apply False.elim assump_8


variable (p6 p2 p1 p7 p5 p3 p4 : Prop)
theorem file98_86906 : ((((((p6 ∨ p6) ∧ (True → False)) ∨ ((p4 → False) → False)) ∧ (((p2 ∧ p4) → (False → False)) ∧ ((p7 → p1) → False))) ∧ ((((p2 ∧ True) → (p3 → p2)) → False) ∨ (((p5 ∧ False) → (True → p4)) → False))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_11
            case intro assump_22 assump_23 =>
              cases assump_9
              case inl assump_28 =>
                have assump_148 : ((p2 ∧ True) → (p3 → p2)) := by
                  intro assump_33
                  intro assump_34
                  cases assump_33
                  case intro assump_37 assump_38 =>
                    exact assump_37
                let assump_32 := assump_28 assump_148
                apply False.elim assump_32
              case inr assump_29 =>
                have assump_149 : ((p5 ∧ False) → (True → p4)) := by
                  intro assump_49
                  intro assump_50
                  cases assump_49
                  case intro assump_53 assump_54 =>
                    apply False.elim assump_54
                let assump_48 := assump_29 assump_149
                apply False.elim assump_48
          case inr assump_17 =>
            cases assump_11
            case intro assump_66 assump_67 =>
              cases assump_9
              case inl assump_72 =>
                have assump_150 : ((p2 ∧ True) → (p3 → p2)) := by
                  intro assump_77
                  intro assump_78
                  cases assump_77
                  case intro assump_81 assump_82 =>
                    exact assump_81
                let assump_76 := assump_72 assump_150
                apply False.elim assump_76
              case inr assump_73 =>
                have assump_151 : ((p5 ∧ False) → (True → p4)) := by
                  intro assump_93
                  intro assump_94
                  cases assump_93
                  case intro assump_97 assump_98 =>
                    apply False.elim assump_98
                let assump_92 := assump_73 assump_151
                apply False.elim assump_92
      case inr assump_13 =>
        cases assump_11
        case intro assump_108 assump_109 =>
          cases assump_9
          case inl assump_114 =>
            have assump_152 : ((p2 ∧ True) → (p3 → p2)) := by
              intro assump_119
              intro assump_120
              cases assump_119
              case intro assump_123 assump_124 =>
                exact assump_123
            let assump_118 := assump_114 assump_152
            apply False.elim assump_118
          case inr assump_115 =>
            have assump_153 : ((p5 ∧ False) → (True → p4)) := by
              intro assump_135
              intro assump_136
              cases assump_135
              case intro assump_139 assump_140 =>
                apply False.elim assump_140
            let assump_134 := assump_115 assump_153
            apply False.elim assump_134


variable (p7 p2 p4 p6 : Prop)
theorem file98_90155 : ((((((False → False) ∧ (False ∧ True)) → False) ∧ (((p7 ∨ True) ∨ (p6 → p2)) ∨ ((p4 ∨ p7) ∧ (p2 → p4)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((False → False) ∧ (False ∧ True)) → False) ∧ (((p7 ∨ True) ∨ (p6 → p2)) ∨ ((p4 ∨ p7) ∧ (p2 → p4)))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p3 p4 p2 p7 p0 p1 p5 p6 : Prop)
theorem file98_90822 : ((((((p2 ∨ p4) ∧ (p0 → False)) ∨ ((p4 ∨ p5) ∧ (p6 ∧ p1))) ∨ (((p7 ∨ p3) → False) → ((p5 → p5) ∨ (False ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 ∨ p4) ∧ (p0 → False)) ∨ ((p4 ∨ p5) ∧ (p6 ∧ p1))) ∨ (((p7 ∨ p3) → False) → ((p5 → p5) ∨ (False ∧ p6)))) := by
    apply Or.inr
    intro assump_5
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p4 p0 : Prop)
theorem file98_91317 : (((((p0 ∧ p1) → False) → ((True ∨ p0) → (True ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_20 : (((p0 ∧ p1) → False) → ((True ∨ p0) → (True ∨ p4))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p7 p5 p1 p0 : Prop)
theorem file98_91799 : (((((p0 → p0) → (False ∨ p5)) ∧ ((p7 → p7) ∧ (False ∧ p7))) ∧ (((p1 → p7) → False) ∧ ((p5 → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p2 p1 p5 p0 p4 p6 p3 : Prop)
theorem file98_92271 : (((((p2 → True) → False) → ((p1 → p5) → False)) → False) → ((((p4 ∧ p1) ∨ (p5 → p5)) → ((p6 ∧ p3) → False)) ∧ (((p1 → True) ∧ (p0 ∧ p2)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_82 : (((p2 → True) → False) → ((p1 → p5) → False)) := by
          intro assump_21
          intro assump_22
          have assump_83 : (p2 → True) := by
            intro assump_28
            apply True.intro
          let assump_27 := assump_21 assump_83
          apply False.elim assump_27
        let assump_20 := assump_1 assump_82
        apply False.elim assump_20
    case inr assump_11 =>
      have assump_84 : (((p2 → True) → False) → ((p1 → p5) → False)) := by
        intro assump_40
        intro assump_41
        have assump_85 : (p2 → True) := by
          intro assump_47
          apply True.intro
        let assump_46 := assump_40 assump_85
        apply False.elim assump_46
      let assump_39 := assump_1 assump_84
      apply False.elim assump_39
  intro assump_54
  cases assump_54
  case intro assump_55 assump_56 =>
    cases assump_56
    case intro assump_59 assump_60 =>
      have assump_86 : (((p2 → True) → False) → ((p1 → p5) → False)) := by
        intro assump_68
        intro assump_69
        have assump_87 : (p2 → True) := by
          intro assump_75
          apply True.intro
        let assump_74 := assump_68 assump_87
        apply False.elim assump_74
      let assump_67 := assump_1 assump_86
      apply False.elim assump_67


variable (p6 : Prop)
theorem file98_93995 : (((((False ∧ p6) ∨ (False ∧ p6)) → False) → False) → False) := by
  intro assump_5
  have assump_23 : (((False ∧ p6) ∨ (False ∧ p6)) → False) := by
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_12
    case inr assump_11 =>
      cases assump_11
      case intro assump_16 assump_17 =>
        apply False.elim assump_16
  let assump_8 := assump_5 assump_23
  apply False.elim assump_8


variable (p6 p4 p2 p7 p0 p1 p5 : Prop)
theorem file98_94555 : (((((p2 → True) ∨ (p5 → False)) ∨ ((p1 ∧ p4) → False)) ∧ (((False → p6) ∨ (p1 ∧ False)) → False)) → ((((p4 → p4) → False) ∧ ((p7 ∨ p2) ∧ (p0 → False))) → False)) := by
  intro assump_17
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_20
    case intro assump_23 assump_24 =>
      cases assump_23
      case inl assump_25 =>
        cases assump_17
        case intro assump_31 assump_32 =>
          cases assump_31
          case inl assump_33 =>
            cases assump_33
            case inl assump_35 =>
              have assump_113 : ((False → p6) ∨ (p1 ∧ False)) := by
                apply Or.inl
                intro assump_42
                apply False.elim assump_42
              let assump_41 := assump_32 assump_113
              apply False.elim assump_41
            case inr assump_36 =>
              have assump_114 : ((False → p6) ∨ (p1 ∧ False)) := by
                apply Or.inl
                intro assump_53
                apply False.elim assump_53
              let assump_52 := assump_32 assump_114
              apply False.elim assump_52
          case inr assump_34 =>
            have assump_115 : ((False → p6) ∨ (p1 ∧ False)) := by
              apply Or.inl
              intro assump_64
              apply False.elim assump_64
            let assump_63 := assump_32 assump_115
            apply False.elim assump_63
      case inr assump_26 =>
        cases assump_17
        case intro assump_74 assump_75 =>
          cases assump_74
          case inl assump_76 =>
            cases assump_76
            case inl assump_78 =>
              have assump_116 : ((False → p6) ∨ (p1 ∧ False)) := by
                apply Or.inl
                intro assump_85
                apply False.elim assump_85
              let assump_84 := assump_75 assump_116
              apply False.elim assump_84
            case inr assump_79 =>
              have assump_117 : ((False → p6) ∨ (p1 ∧ False)) := by
                apply Or.inl
                intro assump_96
                apply False.elim assump_96
              let assump_95 := assump_75 assump_117
              apply False.elim assump_95
          case inr assump_77 =>
            have assump_118 : ((False → p6) ∨ (p1 ∧ False)) := by
              apply Or.inl
              intro assump_107
              apply False.elim assump_107
            let assump_106 := assump_75 assump_118
            apply False.elim assump_106


variable (p3 p7 p0 p4 p6 p5 p1 : Prop)
theorem file98_97086 : ((((((p6 ∨ p6) → False) → ((p6 → False) ∧ (p1 → p6))) → (((False ∧ p5) ∧ (p0 → False)) → False)) → ((((p3 ∨ p5) ∨ (p7 ∨ False)) → False) ∧ (((p7 → p4) ∧ (p3 → p6)) → False))) → False) := by
  intro assump_9
  have assump_63 : ((((p6 ∨ p6) → False) → ((p6 → False) ∧ (p1 → p6))) → (((False ∧ p5) ∧ (p0 → False)) → False)) := by
    intro assump_13
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        apply False.elim assump_17
  let assump_12 := assump_9 assump_63
  let assump_21 := And.right assump_12
  have assump_64 : ((p7 → p4) ∧ (p3 → p6)) := by
    apply And.intro
    intro assump_24
    have assump_65 : ((((p6 ∨ p6) → False) → ((p6 → False) ∧ (p1 → p6))) → (((False ∧ p5) ∧ (p0 → False)) → False)) := by
      intro assump_29
      intro assump_30
      cases assump_30
      case intro assump_31 assump_32 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          apply False.elim assump_33
    let assump_28 := assump_9 assump_65
    let assump_37 := And.left assump_28
    have assump_66 : ((p3 ∨ p5) ∨ (p7 ∨ False)) := by
      apply Or.inr
      apply Or.inl
      exact assump_24
    let assump_38 := assump_37 assump_66
    apply False.elim assump_38
    intro assump_42
    have assump_67 : ((((p6 ∨ p6) → False) → ((p6 → False) ∧ (p1 → p6))) → (((False ∧ p5) ∧ (p0 → False)) → False)) := by
      intro assump_47
      intro assump_48
      cases assump_48
      case intro assump_49 assump_50 =>
        cases assump_49
        case intro assump_51 assump_52 =>
          apply False.elim assump_51
    let assump_46 := assump_9 assump_67
    let assump_55 := And.left assump_46
    have assump_68 : ((p3 ∨ p5) ∨ (p7 ∨ False)) := by
      apply Or.inl
      apply Or.inl
      exact assump_42
    let assump_56 := assump_55 assump_68
    apply False.elim assump_56
  let assump_23 := assump_21 assump_64
  apply False.elim assump_23


variable (p1 p3 p7 p4 p5 : Prop)
theorem file98_99113 : (((((p4 → False) ∨ (p1 → p5)) ∨ ((p7 → False) ∧ (p1 ∨ p7))) ∧ (((p7 ∧ p1) → False) ∨ ((p7 → True) ∨ (p3 ∨ p5)))) → ((((p1 ∨ p4) → (p4 → True)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_6
        case inl assump_13 =>
          have assump_206 : ((p1 ∨ p4) → (p4 → True)) := by
            intro assump_20
            intro assump_21
            apply True.intro
          let assump_19 := assump_2 assump_206
          apply False.elim assump_19
        case inr assump_14 =>
          cases assump_14
          case inl assump_25 =>
            have assump_207 : ((p1 ∨ p4) → (p4 → True)) := by
              intro assump_32
              intro assump_33
              apply True.intro
            let assump_31 := assump_2 assump_207
            apply False.elim assump_31
          case inr assump_26 =>
            cases assump_26
            case inl assump_37 =>
              have assump_208 : ((p1 ∨ p4) → (p4 → True)) := by
                intro assump_44
                intro assump_45
                apply True.intro
              let assump_43 := assump_2 assump_208
              apply False.elim assump_43
            case inr assump_38 =>
              have assump_209 : ((p1 ∨ p4) → (p4 → True)) := by
                intro assump_54
                intro assump_55
                apply True.intro
              let assump_53 := assump_2 assump_209
              apply False.elim assump_53
      case inr assump_10 =>
        cases assump_6
        case inl assump_61 =>
          have assump_210 : ((p1 ∨ p4) → (p4 → True)) := by
            intro assump_68
            intro assump_69
            apply True.intro
          let assump_67 := assump_2 assump_210
          apply False.elim assump_67
        case inr assump_62 =>
          cases assump_62
          case inl assump_73 =>
            have assump_211 : ((p1 ∨ p4) → (p4 → True)) := by
              intro assump_80
              intro assump_81
              apply True.intro
            let assump_79 := assump_2 assump_211
            apply False.elim assump_79
          case inr assump_74 =>
            cases assump_74
            case inl assump_85 =>
              have assump_212 : ((p1 ∨ p4) → (p4 → True)) := by
                intro assump_92
                intro assump_93
                apply True.intro
              let assump_91 := assump_2 assump_212
              apply False.elim assump_91
            case inr assump_86 =>
              have assump_213 : ((p1 ∨ p4) → (p4 → True)) := by
                intro assump_102
                intro assump_103
                apply True.intro
              let assump_101 := assump_2 assump_213
              apply False.elim assump_101
    case inr assump_8 =>
      cases assump_8
      case intro assump_107 assump_108 =>
        cases assump_108
        case inl assump_111 =>
          cases assump_6
          case inl assump_115 =>
            have assump_214 : ((p1 ∨ p4) → (p4 → True)) := by
              intro assump_123
              intro assump_124
              apply True.intro
            let assump_122 := assump_2 assump_214
            apply False.elim assump_122
          case inr assump_116 =>
            cases assump_116
            case inl assump_128 =>
              have assump_215 : ((p1 ∨ p4) → (p4 → True)) := by
                intro assump_136
                intro assump_137
                apply True.intro
              let assump_135 := assump_2 assump_215
              apply False.elim assump_135
            case inr assump_129 =>
              cases assump_129
              case inl assump_141 =>
                have assump_216 : ((p1 ∨ p4) → (p4 → True)) := by
                  intro assump_149
                  intro assump_150
                  apply True.intro
                let assump_148 := assump_2 assump_216
                apply False.elim assump_148
              case inr assump_142 =>
                have assump_217 : ((p1 ∨ p4) → (p4 → True)) := by
                  intro assump_160
                  intro assump_161
                  apply True.intro
                let assump_159 := assump_2 assump_217
                apply False.elim assump_159
        case inr assump_112 =>
          cases assump_6
          case inl assump_167 =>
            have assump_218 : p7 := by
              exact assump_112
            let assump_173 := assump_107 assump_218
            apply False.elim assump_173
          case inr assump_168 =>
            cases assump_168
            case inl assump_177 =>
              have assump_219 : p7 := by
                exact assump_112
              let assump_184 := assump_107 assump_219
              apply False.elim assump_184
            case inr assump_178 =>
              cases assump_178
              case inl assump_188 =>
                have assump_220 : p7 := by
                  exact assump_112
                let assump_194 := assump_107 assump_220
                apply False.elim assump_194
              case inr assump_189 =>
                have assump_221 : p7 := by
                  exact assump_112
                let assump_202 := assump_107 assump_221
                apply False.elim assump_202


variable (p1 p3 p6 p4 : Prop)
theorem file98_104527 : (((((p1 ∨ True) ∨ (p3 ∧ p6)) ∨ ((p6 → False) ∧ (False ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p1 ∨ True) ∨ (p3 ∧ p6)) ∨ ((p6 → False) ∧ (False ∨ p4))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p2 p5 p0 p3 p4 p1 : Prop)
theorem file98_104913 : ((((((p0 ∨ True) → False) ∧ ((p0 ∧ p0) ∧ (p1 → True))) → (((p2 ∧ p7) ∨ (p7 ∨ p3)) → ((p5 ∧ p0) → False))) → ((((p0 ∧ p0) → False) → ((p4 ∧ True) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  have assump_101 : ((((p0 ∨ True) → False) ∧ ((p0 ∧ p0) ∧ (p1 → True))) → (((p2 ∧ p7) ∨ (p7 ∨ p3)) → ((p5 ∧ p0) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_5
          case intro assump_22 assump_23 =>
            cases assump_23
            case intro assump_26 assump_27 =>
              cases assump_26
              case intro assump_28 assump_29 =>
                have assump_102 : (p0 ∨ True) := by
                  apply Or.inl
                  exact assump_29
                let assump_39 := assump_22 assump_102
                apply False.elim assump_39
      case inr assump_15 =>
        cases assump_15
        case inl assump_43 =>
          cases assump_5
          case intro assump_47 assump_48 =>
            cases assump_48
            case intro assump_51 assump_52 =>
              cases assump_51
              case intro assump_53 assump_54 =>
                have assump_103 : (p0 ∨ True) := by
                  apply Or.inl
                  exact assump_54
                let assump_64 := assump_47 assump_103
                apply False.elim assump_64
        case inr assump_44 =>
          cases assump_5
          case intro assump_70 assump_71 =>
            cases assump_71
            case intro assump_74 assump_75 =>
              cases assump_74
              case intro assump_76 assump_77 =>
                have assump_104 : (p0 ∨ True) := by
                  apply Or.inl
                  exact assump_77
                let assump_87 := assump_70 assump_104
                apply False.elim assump_87
  let assump_4 := assump_1 assump_101
  have assump_105 : (((p0 ∧ p0) → False) → ((p4 ∧ True) ∨ (False → False))) := by
    intro assump_92
    apply Or.inr
    intro assump_95
    apply False.elim assump_95
  let assump_91 := assump_4 assump_105
  apply False.elim assump_91


variable (p1 p2 p6 p4 p0 : Prop)
theorem file98_107227 : (((((p1 → False) → False) ∧ ((p0 → p0) → (True → False))) → False) ∨ ((((p1 ∨ p6) → (p4 ∨ p1)) ∧ ((p2 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (p0 → p0) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_3 assump_16
    have assump_17 : True := by
      apply True.intro
    let assump_12 := assump_8 assump_17
    apply False.elim assump_12


variable (p7 p3 p4 p5 p6 p0 p2 p1 : Prop)
theorem file98_107757 : ((((((p4 ∧ True) ∨ (p1 → p0)) → ((False ∧ p4) ∧ (p4 → False))) ∨ (((p2 → False) ∨ (p2 → p3)) → False)) ∧ ((((p5 ∨ p7) → False) → ((p4 ∧ p3) ∨ (False → False))) ∧ (((p6 → True) → False) ∧ ((False ∧ p4) ∧ (p4 → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
    case inr assump_5 =>
      cases assump_3
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          cases assump_29
          case intro assump_32 assump_33 =>
            cases assump_32
            case intro assump_34 assump_35 =>
              apply False.elim assump_34


variable (p5 p6 p3 p0 : Prop)
theorem file98_108801 : (((((p5 ∨ p5) → (True ∧ p3)) → ((False ∧ p3) → False)) → (((p6 → False) ∧ (True → False)) ∧ ((p0 ∨ p0) → False))) → False) := by
  intro assump_1
  have assump_18 : (((p5 ∨ p5) → (True ∧ p3)) → ((False ∧ p3) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_18
  let assump_11 := And.left assump_4
  let assump_12 := And.right assump_11
  have assump_19 : True := by
    apply True.intro
  let assump_14 := assump_12 assump_19
  apply False.elim assump_14


variable (p3 p7 p1 p2 p5 p6 p4 p0 : Prop)
theorem file98_109448 : (((((p2 ∨ p7) ∨ (p7 → False)) → False) ∧ (((p0 ∧ p6) ∧ (True → False)) → ((p3 ∨ p3) → (p3 ∨ p1)))) → ((((p7 → p2) ∨ (p7 → False)) ∧ ((p6 → p4) → (p4 ∨ p2))) → (((p7 → p5) ∧ (p0 ∧ True)) ∨ ((False ∨ True) ∧ (p2 ∧ p5))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        have assump_73 : ((p2 ∨ p7) ∨ (p7 → False)) := by
          apply Or.inr
          intro assump_28
          have assump_74 : ((p2 ∨ p7) ∨ (p7 → False)) := by
            apply Or.inl
            apply Or.inr
            exact assump_28
          let assump_33 := assump_11 assump_74
          apply False.elim assump_33
        let assump_27 := assump_11 assump_73
        apply False.elim assump_27
    case inr assump_6 =>
      cases assump_1
      case intro assump_44 assump_45 =>
        have assump_75 : ((p2 ∨ p7) ∨ (p7 → False)) := by
          apply Or.inr
          intro assump_61
          have assump_76 : ((p2 ∨ p7) ∨ (p7 → False)) := by
            apply Or.inl
            apply Or.inr
            exact assump_61
          let assump_66 := assump_44 assump_76
          apply False.elim assump_66
        let assump_60 := assump_44 assump_75
        apply False.elim assump_60


variable (p1 p0 p4 p5 p2 p3 : Prop)
theorem file98_110828 : ((((((p0 ∨ p3) → (p5 → False)) → ((p4 ∧ p0) → (p1 → p4))) ∨ (((True → p4) ∧ (p2 ∧ p3)) → ((p0 → p1) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p0 ∨ p3) → (p5 → False)) → ((p4 ∧ p0) → (p1 → p4))) ∨ (((True → p4) ∧ (p2 ∧ p3)) → ((p0 → p1) → (p5 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      exact assump_10
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p1 p3 p4 p0 p5 p2 : Prop)
theorem file98_111409 : (((((p2 ∧ False) → (p4 → False)) → False) → False) ∨ ((((p1 → False) → (p3 ∧ p4)) ∧ ((p5 ∨ True) → (p2 ∨ p5))) ∧ (((p1 → False) → (p7 → False)) ∨ ((p0 ∧ p5) ∧ (p1 → p4))))) := by
  apply Or.inl
  intro assump_9
  have assump_26 : ((p2 ∧ False) → (p4 → False)) := by
    intro assump_13
    intro assump_14
    cases assump_13
    case intro assump_17 assump_18 =>
      apply False.elim assump_18
  let assump_12 := assump_9 assump_26
  apply False.elim assump_12


variable (p6 p1 p4 p3 p7 p5 p2 p0 : Prop)
theorem file98_111939 : (((((True ∨ False) → False) ∨ ((True ∨ p1) ∧ (True ∧ p4))) ∧ (((p1 → False) ∨ (p7 → False)) ∨ ((False ∧ p3) → (p2 ∨ p3)))) → ((((p2 ∨ p6) ∨ (True → p6)) → ((p0 ∧ False) → False)) ∨ (((p0 → p5) → (p0 ∧ p2)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          intro assump_14
          intro assump_15
          cases assump_15
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
        case inr assump_11 =>
          apply Or.inl
          intro assump_24
          intro assump_25
          cases assump_25
          case intro assump_26 assump_27 =>
            apply False.elim assump_27
      case inr assump_9 =>
        apply Or.inl
        intro assump_34
        intro assump_35
        cases assump_35
        case intro assump_36 assump_37 =>
          apply False.elim assump_37
    case inr assump_5 =>
      cases assump_5
      case intro assump_42 assump_43 =>
        cases assump_42
        case inl assump_44 =>
          cases assump_43
          case intro assump_48 assump_49 =>
            cases assump_3
            case inl assump_54 =>
              cases assump_54
              case inl assump_56 =>
                apply Or.inl
                intro assump_60
                intro assump_61
                cases assump_61
                case intro assump_62 assump_63 =>
                  apply False.elim assump_63
              case inr assump_57 =>
                apply Or.inl
                intro assump_70
                intro assump_71
                cases assump_71
                case intro assump_72 assump_73 =>
                  apply False.elim assump_73
            case inr assump_55 =>
              apply Or.inl
              intro assump_80
              intro assump_81
              cases assump_81
              case intro assump_82 assump_83 =>
                apply False.elim assump_83
        case inr assump_45 =>
          cases assump_43
          case intro assump_90 assump_91 =>
            cases assump_3
            case inl assump_96 =>
              cases assump_96
              case inl assump_98 =>
                apply Or.inl
                intro assump_102
                intro assump_103
                cases assump_103
                case intro assump_104 assump_105 =>
                  apply False.elim assump_105
              case inr assump_99 =>
                apply Or.inl
                intro assump_112
                intro assump_113
                cases assump_113
                case intro assump_114 assump_115 =>
                  apply False.elim assump_115
            case inr assump_97 =>
              apply Or.inl
              intro assump_122
              intro assump_123
              cases assump_123
              case intro assump_124 assump_125 =>
                apply False.elim assump_125


variable (p1 p6 p0 p7 p3 p5 : Prop)
theorem file98_115050 : (((((p6 ∧ p1) → False) → ((p0 ∧ p1) → (p3 ∨ p1))) ∧ (((p5 ∨ True) ∨ (p0 → False)) → False)) → ((((p6 ∨ p6) → (True → False)) ∨ ((p7 ∨ True) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      have assump_29 : ((p5 ∨ True) ∨ (p0 → False)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_13 := assump_8 assump_29
      apply False.elim assump_13
  case inr assump_4 =>
    cases assump_1
    case intro assump_19 assump_20 =>
      have assump_30 : ((p5 ∨ True) ∨ (p0 → False)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_25 := assump_20 assump_30
      apply False.elim assump_25


