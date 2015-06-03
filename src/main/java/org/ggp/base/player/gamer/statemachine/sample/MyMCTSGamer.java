package org.ggp.base.player.gamer.statemachine.sample;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.propnet.SamplePropNetStateMachine;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

import java.util.*;

/**
 * Created by hy on 2015/6/3.
 */
public class MyMCTSGamer extends SampleGamer
{
    public static Random rand = new Random();
    private StateMachine sm;
    private Role role;
    private long timeLimit;

    private UCTNode dummy = new UCTNode();

    private class UCTNode
    {
        private List<UCTNode> children;
        private UCTNode parent;
        private MachineState state;
        private int visitCount, rank;
        private boolean played;
        private final double miniVal = 1e-6;
        private List<Move> lastJointMove;
        private List<List<Move>> nextJointMoves;
        private int randomPlayProgress;

        public UCTNode(MachineState initialStatus)
                throws MoveDefinitionException
        {
            played = false;
            children = new ArrayList<UCTNode>();
            state = initialStatus;
            nextJointMoves = sm.getLegalJointMoves(state);
            randomPlayProgress = 0;
            visitCount = 0;
            rank = 0;
        }

        private UCTNode()
        {
            // DUMMY Only!
            visitCount = -1;
            rank = Integer.MIN_VALUE;
        }

        private UCTNode(UCTNode parent, List<Move> jointMove)
                throws TransitionDefinitionException, MoveDefinitionException
        {
            played = false;
            children = new ArrayList<UCTNode>();
            visitCount = 0;
            rank = 0;
            lastJointMove = jointMove;
            this.parent = parent;
            state = sm.getNextState(parent.state, jointMove);
            nextJointMoves = sm.getLegalJointMoves(state);
            randomPlayProgress = 0;
        }

        public void BecomeOrphan()
        {
            // this.visitCount = 0;
            this.parent = null;
        }

        public UCTNode GetMostPlayedMove()
        {
            UCTNode best = dummy;
            for (UCTNode node : children)
                if (node.visitCount >= best.visitCount)
                    best = node;
            return best;
        }

        public UCTNode GetRankHighestMove()
        {
            UCTNode best = dummy;
            for (UCTNode node : children)
            {
                if (node.rank > best.rank)
                    best = node;
            }
            return best;
        }

        private UCTNode GetBestMove()
        {
            double bestVal = Double.NEGATIVE_INFINITY, currVal;
            UCTNode best = null;
            for (UCTNode node : children)
            {
                currVal = node.rank / (node.visitCount + miniVal) +
                        Math.sqrt(2 * Math.log(visitCount + 1) / (node.visitCount + miniVal)) + miniVal * rand.nextDouble();
                if (currVal > bestVal)
                {
                    bestVal = currVal;
                    best = node;
                }
            }
            return best;
        }

        public UCTNode FindNode(MachineState byState)
        {
            for (UCTNode node : children)
            {
                if (node.state.equals(byState))
                    return node;
            }
            return null;
        }

        public void FlatUCT()
        {
            if (children.isEmpty())
                while (randomPlayProgress < nextJointMoves.size())
                {
                    // 扩展结点
                    UCTNode curr;
                    try
                    {
                        curr = new UCTNode(this, nextJointMoves.get(randomPlayProgress));
                        children.add(curr);
                    }
                    catch (Exception e)
                    {
                    }
                    randomPlayProgress++;
                }
            for (UCTNode n : children)
            {
                // 模拟对局
                UCTNode curr = n;
                int result = curr.RandomPlay();
                while (curr.parent != null)
                {
                    curr.visitCount++;
                    curr.rank += result;
                    curr = curr.parent;
                }
                curr.visitCount++;
            }
        }

        public void AnalyzeInner(int depthLeft)
        {
            int result = 0;
            if (children.isEmpty())
                if (played)
                    while (randomPlayProgress < nextJointMoves.size())
                    {
                        // 扩展结点
                        UCTNode curr;
                        try
                        {
                            curr = new UCTNode(this, nextJointMoves.get(randomPlayProgress));
                            children.add(curr);
                        }
                        catch (Exception e)
                        {
                        }
                        randomPlayProgress++;
                    }
                else
                {
                    // 模拟对局
                    UCTNode curr = this;
                    result = curr.RandomPlay();
                    while (curr.parent != null)
                    {
                        curr.visitCount++;
                        curr.rank += result;
                        curr = curr.parent;
                    }
                    curr.visitCount++;
                    played = true;
                    return;
                }
            // 递归探索最佳子节点
            if (!sm.isTerminal(state) && !children.isEmpty() && depthLeft > 0)
            {
                if (visitCount == 0)
                    children.get(rand.nextInt(children.size())).AnalyzeInner(depthLeft - 1);
                else
                    GetBestMove().AnalyzeInner(depthLeft - 1);
            }
            else if (sm.isTerminal(state))
            {
                UCTNode curr = this;
                try
                {
                    result = sm.getGoal(state, role);
                    while (curr.parent != null)
                    {
                        curr.visitCount++;
                        curr.rank += result;
                        curr = curr.parent;
                    }
                    curr.visitCount++;
                }
                catch (Exception e)
                {
                }
            }
        }

        private int RandomPlay()
        {
            try
            {
                MachineState finalState = sm.performDepthCharge(state, null);
                return sm.getGoal(finalState, role);
            }
            catch (Exception e)
            {
                return 0;
            }
        }
    }

    private UCTNode node;

    @Override
    public void stateMachineMetaGame(long timeout)
            throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException
    {
        sm = getStateMachine();
        role = getRole();
        node = new UCTNode(sm.getInitialState());
        node.AnalyzeInner(0);
    }

    @Override
    public Move stateMachineSelectMove(long timeout)
    {
        timeLimit = timeout - 2000;
        sm = getStateMachine();
        role = getRole();
        node.AnalyzeInner(0);
        if (!node.state.equals(getCurrentState()))
        {
            node = node.FindNode(getCurrentState());
            node.BecomeOrphan();
        }
        while (System.currentTimeMillis() < timeLimit)
        {
            node.AnalyzeInner(Integer.MAX_VALUE);
            // node.FlatUCT();
        }
        return node.GetRankHighestMove().lastJointMove.get(sm.getRoleIndices().get(role));
    }

    @Override
    public StateMachine getInitialStateMachine()
    {
        return new CachedStateMachine(new ProverStateMachine());
    }
}
