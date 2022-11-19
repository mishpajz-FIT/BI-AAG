#ifndef __PROGTEST__

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <variant>
#include <vector>

using State = unsigned int;
using Symbol = uint8_t;

struct NFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, std::set<State>> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};

struct DFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, State> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};

#endif

static const State nullState = -1;

NFA complete(const NFA& a) {
    NFA result(a);

    // Create new nullState in automata
    result.m_States.insert(nullState);
    for (Symbol s: result.m_Alphabet) {
        result.m_Transitions[std::make_pair(nullState, s)] = { nullState };
    }

    // BFS through automata and complete all transitions for all symbols of alphabet
    std::set<State> completed;
    std::queue<State> queue;

    queue.push(result.m_InitialState);
    completed.insert(result.m_InitialState);
    completed.insert(nullState);

    while (queue.size() > 0) {
        State top = queue.front();
        queue.pop();

        for (Symbol s : result.m_Alphabet) {
            std::pair<State, Symbol> transitionKey(top, s);
            auto transition = result.m_Transitions.find(transitionKey);

            // If transition for this symbol doesnt exist, complete it to nullState
            if (transition == result.m_Transitions.end()) {
                result.m_Transitions[transitionKey] = { nullState };
                continue;
            }

            // If transition for this symbol does exist, add destination state to queue and continue bfs
            for (State destination : transition->second) {
                if (completed.count(destination) == 0) {
                    completed.insert(destination);
                    queue.push(destination);
                }
            }
        }
    }

    return result;
}

NFA parallelRun(const NFA & a, const NFA & b, bool finalStatesAreUnified) {
    using DoubleState = std::pair<State, State>; // States are pairs of states, where lhs is state in a and rhs is state in b

    std::map<std::pair<DoubleState, Symbol>, std::set<DoubleState>> newTransitions; // New generated transitions
    DoubleState newInitialState = { a.m_InitialState, b.m_InitialState };

    // BFS through automata and merge all states into doublestates
    std::set<DoubleState> visited;
    std::queue<DoubleState> queue;

    queue.push(newInitialState);
    visited.insert(newInitialState);

    while (queue.size() > 0) {
        DoubleState top = queue.front();
        queue.pop();

        for (Symbol s : a.m_Alphabet) {
            // Find transtions for each state in doublestate in their automata
            auto transitionA = a.m_Transitions.find(std::make_pair(top.first, s));
            auto transitionB = a.m_Transitions.find(std::make_pair(top.second, s));

            if ((transitionA == a.m_Transitions.end()) || (transitionB == b.m_Transitions.end())) {
                continue;
            }

            // Create combinations of all transition destinations for a automata with all transition desitnations
            // for b automata (for each symbol) and add it as new transition for this doublestate,
            // then continue BFS for each new transition destination
            for (State destinationA : transitionA->second) {
                for (State destinationB : transitionB->second) {
                    DoubleState destination = { destinationA, destinationB };
                    newTransitions[std::make_pair(top, s)].insert(destination);
                    if (visited.count(destination) == 0) {
                        visited.insert(destination);
                        queue.push(destination);
                    }
                }
            }
        }
    }

    NFA result;
    result.m_Alphabet = a.m_Alphabet;

    // Map each doublestate to new state for result automata
    std::map<DoubleState, State> newStatesMapping;
    State newStateValue = 0;
    for (DoubleState const & doubleState : visited) {
        result.m_States.insert(newStateValue);
        newStatesMapping[doubleState] = newStateValue;

        // Decide if new state is final state based on function parameter
        bool finalInA = (a.m_FinalStates.count(doubleState.first) > 0);
        bool finalInB = (b.m_FinalStates.count(doubleState.second) > 0);

        if (finalStatesAreUnified) { // States in both a and b need to be final for new state to be final
            if (finalInA && finalInB) {
                result.m_FinalStates.insert(newStateValue);
            }
        } else { // Only one state needs to be final for new state to be final
            if (finalInA || finalInB) {
                result.m_FinalStates.insert(newStateValue);
            }
        }

        newStateValue++;
    }

    result.m_InitialState = newStatesMapping[newInitialState]; // Assign initial state in result

    // Create new transitions in result based on transitions with doublestates converted to new states  
    for (auto it = newTransitions.begin(); it != newTransitions.end(); it++) {
        for (DoubleState const & transitionDestination : it->second) {
            DoubleState oldState = it->first.first;
            Symbol symbol = it->first.second;
            State newDestination = newStatesMapping[transitionDestination];
            result.m_Transitions[std::make_pair(newStatesMapping[oldState], symbol)].insert(newDestination);
        }
    }

    return result;
}

DFA determinize(const NFA & nfa) {
    using MultiState = std::set<State>; // States are sets of states

    DFA result;
    result.m_Alphabet = nfa.m_Alphabet;
    result.m_InitialState = nfa.m_InitialState;

    std::map<std::pair<MultiState, Symbol>, MultiState> newTransitions; // New generated transitions

    // BFS through automata and generate new states from sets of states
    std::queue<MultiState> queue;
    std::set<MultiState> visited;

    visited.insert({ nfa.m_InitialState });
    queue.push({ nfa.m_InitialState });

    while (queue.size() > 0) {
        MultiState top = queue.front();
        queue.pop();

        for (Symbol symbol : nfa.m_Alphabet) {
            MultiState newDestination;

            // Generate new destination as multistate from all destinations for all states in this mulitstate
            for (State substate : top) {
                auto oldTransition = nfa.m_Transitions.find(std::make_pair(substate, symbol));

                if (oldTransition == nfa.m_Transitions.end()) {
                    continue;
                }

                for (State subDestination: oldTransition->second) {
                    newDestination.insert(subDestination);
                }
            }

            // Add new multistate as transition destination and continue BFS
            if (newDestination.size() > 0) {
                newTransitions[std::make_pair(top, symbol)] = newDestination;

                if (visited.count(newDestination) == 0) {
                    visited.insert(newDestination);
                    queue.push(newDestination);
                }
            }
        }
    }

    // Map each multistate to new state for result automata
    std::map<MultiState, State> newStatesMapping;
    State newStateValue = 0;
    for (MultiState const & multiState : visited) {
        result.m_States.insert(newStateValue);
        newStatesMapping[multiState] = newStateValue;

        // If one of substates in multistate is final, set for new state in result to be final
        for (State substate: multiState) {
            if (nfa.m_FinalStates.count(substate) > 0) {
                result.m_FinalStates.insert(newStateValue);
                break;
            }
        }

        newStateValue++;
    }

    result.m_InitialState = newStatesMapping[{ nfa.m_InitialState }]; // Assign initial state in result

     // Create new transitions in result based on transitions with multistates converted to new states  
    for (auto it = newTransitions.begin(); it != newTransitions.end(); it++) {
        result.m_Transitions[std::make_pair(newStatesMapping[it->first.first], it->first.second)] = newStatesMapping[it->second];
    }

    return result;
}

DFA removeUseless(const DFA & dfa) {

    // Reverse all transitions
    std::map<State, std::set<State>> reverseTransitions;
    for (auto it = dfa.m_Transitions.begin(); it != dfa.m_Transitions.end(); it++) {
        reverseTransitions[it->second].insert(it->first.first);
    }

    // Perform BFS from final states, store reached (useful) states
    std::queue<State> queue;
    std::set<State> useful;

    for (State final : dfa.m_FinalStates) {
        queue.push(final);
        useful.insert(final);
    }

    while (queue.size() > 0) {
        State top = queue.front();
        queue.pop();

        for (State origin : reverseTransitions[top]) {
            if (useful.count(origin) == 0) {
                useful.insert(origin);
                queue.push(origin);
            }
        }
    }

    // Create new automata
    DFA result;
    result.m_InitialState = dfa.m_InitialState;
    result.m_Alphabet = dfa.m_Alphabet;
    result.m_States = { dfa.m_InitialState };

    // Perofrm BFS from initial state, only adding states and transitions that are usefull
    std::queue<State> newQueue;
    newQueue.push(dfa.m_InitialState);
    std::swap(queue, newQueue);

    while (queue.size() > 0) {
        State top = queue.front();
        queue.pop();

        if (dfa.m_FinalStates.count(top) > 0) { // Check if state is final and add it to final states
            result.m_FinalStates.insert(top);
        }

        // Find all transitions (for all symbols of alphabet)
        for (Symbol symbol : result.m_Alphabet) {
            auto transition = dfa.m_Transitions.find(std::make_pair(top, symbol));

            if (transition == dfa.m_Transitions.end()) {
                continue;
            }

            State destination = transition->second;
            if (useful.count(destination) > 0) { // If state is useful, add transition to result
                result.m_Transitions[std::make_pair(top, symbol)] = destination;

                if (result.m_States.count(destination) == 0) { // If state has not been processed, continue BFS on it
                    result.m_States.insert(destination);
                    queue.push(destination);
                }
            }
        }
    }

    return result;
}

DFA minimize(const DFA & dfa) {
    using Transition = std::pair<Symbol, State>;

    std::map<State, State> equivalenceStates;

    for (State state : dfa.m_States) {
        if (dfa.m_FinalStates.count(state) > 0) {
            equivalenceStates[state] = 1;
        } else {
            equivalenceStates[state] = 0;
        }
    }
    State nextAvailableState = 2;

    bool changed = false;
    do {
        changed = false;

        std::map<State, std::map<State, std::set<Transition>>> equivalenceTable;

        for (State state : dfa.m_States) {

            State equivalentState = equivalenceStates[state];

            for (Symbol symbol : dfa.m_Alphabet) {
                auto transition = dfa.m_Transitions.find(std::make_pair(state, symbol));

                if (transition == dfa.m_Transitions.end()) {
                    continue;
                }

                (equivalenceTable[equivalentState])[state].insert(std::make_pair(symbol, equivalenceStates[transition->second]));
            }
        }

        for (auto it = equivalenceTable.begin(); it != equivalenceTable.end(); it++) {
            State equivalentState = it->first;
            std::map<std::set<Transition>, State> newStates;

            for (auto itIn = it->second.begin(); itIn != it->second.end(); itIn++) {
                if (itIn == it->second.begin()) {
                    newStates[itIn->second] = equivalentState;
                    continue;
                }

                if (newStates.count(itIn->second) > 0) {
                    equivalenceStates[itIn->first] = newStates[itIn->second];
                    continue;
                }

                newStates[itIn->second] = nextAvailableState;
                equivalenceStates[itIn->first] = nextAvailableState;
                nextAvailableState++;
                changed = true;
            }
        }

    } while (changed);

    DFA result;
    result.m_InitialState = equivalenceStates[dfa.m_InitialState];
    result.m_Alphabet = dfa.m_Alphabet;

    for (State state : dfa.m_States) {
        State equivalentState = equivalenceStates[state];

        result.m_States.insert(equivalentState);

        if (dfa.m_FinalStates.count(state) > 0) {
            result.m_FinalStates.insert(equivalentState);
        }

        for (Symbol symbol : dfa.m_Alphabet) {
            auto transition = dfa.m_Transitions.find(std::make_pair(state, symbol));

            if (transition == dfa.m_Transitions.end()) {
                continue;
            }

            result.m_Transitions[std::make_pair(equivalentState, symbol)] = equivalenceStates[transition->second];
        }
    }

    return result;
}

void unifyAlphabets(NFA & a, NFA & b) {
    std::set<Symbol> newAlphabet;
    for (Symbol s : a.m_Alphabet) {
        newAlphabet.insert(s);
    }
    for (Symbol s : b.m_Alphabet) {
        newAlphabet.insert(s);
    }

    a.m_Alphabet = newAlphabet;
    b.m_Alphabet = newAlphabet;
}

DFA unify(const NFA & a, const NFA & b) {
    NFA copyA(a);
    NFA copyB(b);
    unifyAlphabets(copyA, copyB);

    return minimize(determinize(parallelRun(complete(copyA), complete(copyB), false)));
}

DFA intersect(const NFA & a, const NFA & b) {
    NFA copyA(a);
    NFA copyB(b);
    unifyAlphabets(copyA, copyB);

    return minimize(determinize(parallelRun(copyA, copyB, true)));
}

#ifndef __PROGTEST__

// You may need to update this function or the sample data if your state naming strategy differs.
bool operator==(const DFA& a, const DFA& b)
{
    return std::tie(a.m_States, a.m_Alphabet, a.m_Transitions, a.m_InitialState, a.m_FinalStates) == std::tie(b.m_States, b.m_Alphabet, b.m_Transitions, b.m_InitialState, b.m_FinalStates);
}

int main()
{
    NFA a1{
        {0, 1, 2},
        {'a', 'b'},
        {
            {{0, 'a'}, {0, 1}},
            {{0, 'b'}, {0}},
            {{1, 'a'}, {2}},
        },
        0,
        {2},
    };
    NFA a2{
        {0, 1, 2},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{1, 'a'}, {2}},
            {{2, 'a'}, {2}},
            {{2, 'b'}, {2}},
        },
        0,
        {2},
    };
    DFA a{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{1, 'a'}, {2}},
            {{2, 'a'}, {2}},
            {{2, 'b'}, {3}},
            {{3, 'a'}, {4}},
            {{3, 'b'}, {3}},
            {{4, 'a'}, {2}},
            {{4, 'b'}, {3}},
        },
        0,
        {2},
    };
    assert(intersect(a1, a2) == a);

    NFA b1{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{0, 'b'}, {2}},
            {{2, 'a'}, {2, 3}},
            {{2, 'b'}, {2}},
            {{3, 'a'}, {4}},
        },
        0,
        {1, 4},
    };
    NFA b2{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'b'}, {1}},
            {{1, 'a'}, {2}},
            {{2, 'b'}, {3}},
            {{3, 'a'}, {4}},
            {{4, 'a'}, {4}},
            {{4, 'b'}, {4}},
        },
        0,
        {4},
    };
    DFA b{
        {0, 1, 2, 3, 4, 5, 6, 7, 8},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{0, 'b'}, {2}},
            {{2, 'a'}, {3}},
            {{2, 'b'}, {4}},
            {{3, 'a'}, {5}},
            {{3, 'b'}, {6}},
            {{4, 'a'}, {7}},
            {{4, 'b'}, {4}},
            {{5, 'a'}, {5}},
            {{5, 'b'}, {4}},
            {{6, 'a'}, {8}},
            {{6, 'b'}, {4}},
            {{7, 'a'}, {5}},
            {{7, 'b'}, {4}},
            {{8, 'a'}, {8}},
            {{8, 'b'}, {8}},
        },
        0,
        {1, 5, 8},
    };
    assert(unify(b1, b2) == b);

    NFA c1{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{0, 'b'}, {2}},
            {{2, 'a'}, {2, 3}},
            {{2, 'b'}, {2}},
            {{3, 'a'}, {4}},
        },
        0,
        {1, 4},
    };
    NFA c2{
        {0, 1, 2},
        {'a', 'b'},
        {
            {{0, 'a'}, {0}},
            {{0, 'b'}, {0, 1}},
            {{1, 'b'}, {2}},
        },
        0,
        {2},
    };
    DFA c{
        {0},
        {'a', 'b'},
        {},
        0,
        {},
    };
    assert(intersect(c1, c2) == c);

    NFA d1{
        {0, 1, 2, 3},
        {'i', 'k', 'q'},
        {
            {{0, 'i'}, {2}},
            {{0, 'k'}, {1, 2, 3}},
            {{0, 'q'}, {0, 3}},
            {{1, 'i'}, {1}},
            {{1, 'k'}, {0}},
            {{1, 'q'}, {1, 2, 3}},
            {{2, 'i'}, {0, 2}},
            {{3, 'i'}, {3}},
            {{3, 'k'}, {1, 2}},
        },
        0,
        {2, 3},
    };
    NFA d2{
        {0, 1, 2, 3},
        {'i', 'k'},
        {
            {{0, 'i'}, {3}},
            {{0, 'k'}, {1, 2, 3}},
            {{1, 'k'}, {2}},
            {{2, 'i'}, {0, 1, 3}},
            {{2, 'k'}, {0, 1}},
        },
        0,
        {2, 3},
    };
    DFA d{
        {0, 1, 2, 3},
        {'i', 'k', 'q'},
        {
            {{0, 'i'}, {1}},
            {{0, 'k'}, {2}},
            {{2, 'i'}, {3}},
            {{2, 'k'}, {2}},
            {{3, 'i'}, {1}},
            {{3, 'k'}, {2}},
        },
        0,
        {1, 2, 3},
    };
    assert(intersect(d1, d2) == d);
}
#endif
