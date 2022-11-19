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

    //BFS through automata and complete all transitions for all symbols of alphabet
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

NFA parallel_run(const NFA & a, const NFA & b, bool finalStatesAreUnified) {
    using DoubleState = std::pair<State, State>;

    std::map<std::pair<DoubleState, Symbol>, std::set<DoubleState>> newTransitions;
    DoubleState newInitialState = { a.m_InitialState, b.m_InitialState };

    std::set<DoubleState> visited;
    std::queue<DoubleState> queue;

    queue.push(newInitialState);
    visited.insert(newInitialState);

    while (queue.size() > 0) {
        DoubleState top = queue.front();
        queue.pop();

        for (Symbol s : a.m_Alphabet) {
            auto transitionA = a.m_Transitions.find(std::make_pair(top.first, s));
            auto transitionB = a.m_Transitions.find(std::make_pair(top.second, s));

            if ((transitionA == a.m_Transitions.end()) || (transitionB == b.m_Transitions.end())) {
                continue;
            }

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

    NFA newNFA;
    newNFA.m_Alphabet = a.m_Alphabet;

    std::map<DoubleState, State> newStatesMapping;
    State newStateValue = 0;
    for (DoubleState const & doubleState : visited) {
        newNFA.m_States.insert(newStateValue);
        newStatesMapping[doubleState] = newStateValue;

        bool finalInA = (a.m_FinalStates.count(doubleState.first) > 0);
        bool finalInB = (b.m_FinalStates.count(doubleState.second) > 0);

        if (finalStatesAreUnified) {
            if (finalInA && finalInB) {
                newNFA.m_FinalStates.insert(newStateValue);
            }
        } else {
            if (finalInA || finalInB) {
                newNFA.m_FinalStates.insert(newStateValue);
            }
        }

        newStateValue++;
    }

    newNFA.m_InitialState = newStatesMapping[newInitialState];

    for (auto it = newTransitions.begin(); it != newTransitions.end(); it++) {
        for (DoubleState const & transitionDestination : it->second) {
            DoubleState oldState = it->first.first;
            Symbol symbol = it->first.second;
            State newDestination = newStatesMapping[transitionDestination];
            newNFA.m_Transitions[std::make_pair(newStatesMapping[oldState], symbol)].insert(newDestination);
        }
    }

    return newNFA;
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

    NFA completedA = complete(copyA);
    NFA completedB = complete(copyB);

    NFA unified = parallel_run(completedA, completedB, false);
}

DFA intersect(const NFA & a, const NFA & b) {
    NFA copyA(a);
    NFA copyB(b);
    unifyAlphabets(copyA, copyB);

    NFA intersected = parallel_run(copyA, copyB, true);
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
