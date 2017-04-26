# This file is part of agora-tally.
# Copyright (C) 2017  Agora Voting SL <agora@agoravoting.com>

# agora-tally is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published by
# the Free Software Foundation, either version 3 of the License.

# agora-tally  is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.

# You should have received a copy of the GNU Affero General Public License
# along with agora-tally.  If not, see <http://www.gnu.org/licenses/>.

from __future__ import unicode_literals
import random
import copy
import uuid
import sys
import codecs
import os
from operator import itemgetter
from collections import defaultdict

from ..ballot_counter.ballots import Ballots
from ..ballot_counter.plugins import getMethodPlugins

from .base import BaseVotingSystem, BaseTally, BlankVoteException


class STVHareClark(BaseVotingSystem):
    '''
    Defines the helper functions that allows agora to manage an OpenSTV-based
     STV Hare Clark voting system.
    '''

    @staticmethod
    def get_id():
        '''
        Returns the identifier of the voting system, used internally to
        discriminate  the voting system used in an election
        '''
        return 'stv-hare-clark'

    @staticmethod
    def get_description():
        return _('STV Hare Clark Count voting')

    @staticmethod
    def create_tally(election, question_num):
        '''
        Create object that helps to compute the tally
        '''
        return STVHareClarkTally(election, question_num)

class STVHareClarkTally(BaseTally):
    '''
    Class used to tally an election
    '''
    ballots_file = None
    ballots_path = ""

    # array containing the current list of ballots
    ballots = []

    num_winners = -1

    method_name = "STVHareClark"

    # report object
    report = None

    def init(self):
        self.ballots = dict()

    def parse_vote(self, number, question, withdrawals=[]):
        vote_str = str(number)
        tab_size = len(str(len(question['answers']) + 2))

        # fix add zeros
        if len(vote_str) % tab_size != 0:
            num_zeros = (tab_size - (len(vote_str) % tab_size)) % tab_size
            vote_str = "0" * num_zeros + vote_str

        ret = []
        for i in range(int(len(vote_str) / tab_size)):
            option = int(vote_str[i*tab_size: (i+1)*tab_size]) - 1

            if option in withdrawals:
                continue
            # blank vote
            elif option == len(question['answers']) + 1:
                raise BlankVoteException()
            # invalid vote
            elif option < 0 or option >= len(question['answers']):
                raise Exception()
            ret.append(option)

        # detect invalid vote
        if len(ret) < question['min'] or len(set(ret)) != len(ret):
            raise Exception()
        if len(ret) > question['max']:
            if "truncate-max-overload" in question and question["truncate-max-overload"]:
                ret = ret[:question['max']]
            else:
                raise Exception()

        return ret

    def pre_tally(self, questions):
        '''
        Function called once before the tally begins
        '''

    def add_vote(self, voter_answers, questions, is_delegated):
        '''
        Add to the count a vote from a voter
        '''
        answers = copy.deepcopy(voter_answers[self.question_num]['choices'])
        # we got ourselves an invalid vote, don't count it
        if -1 in answers:
            return

        # don't count blank/invalid votes
        if len(answers) > 0:
            # add ballot
            self.ballots.append(answers)

    # removes an option from all ballots
    # also removes void ballots
    def remove_option_from_ballots(self, ballots, candidate_option):
        # remove all occurences of the candidate in the ballots
        for index, ballot in enumerate(ballots):
            newballot = [
                option 
                for option in ballot
                if option != candidate_option]
            ballot[index] = newballot
        # remove ballots with no option selected
        while [] in ballots:
            ballots.remove([])

    # list of votes to share
    # get the list of ballots where the candidate option is the first option
    # and with more than one option selected
    def get_votes_to_share(self, ballots, candidate_option):
         return [
             ballot
             for ballot in ballots
             if ballot[0] == candidate_option and 
                 len(ballot) > 1]

    # number of times the second_candidate_option appears as second option
    def ocurrence_second_candidate(self, votes_to_share, second_candidate_option):
        times_appearing_second = 0
        for ballot in votes_to_share:
            if second_candidate_option == ballot[1]:
                 times_appearing_second += 1
        return times_appearing_second

    def perform_round(
        self,
        question,
        ballots,
        winners,
        losers,
        remaining_vacant_seats,
        candidates,
        quota,
        round_count,
        continue_round):
        this_round_added_winners = False
        # if there are no remaining winner seats, we have nothing to do
        if 0 == remaining_vacant_seats:
            continue_round = False
            return

        someone_surpasses_quota = False
        for candidate in candidates[:]:
            # if there are no remaining winner seats, we have nothing to do
            if 0 == remaining_vacant_seats:
                continue_round = False
                return

            # if the number of vacant seats is the number of candidates, all of them
            # are winners
            if len(candidates) == remaining_vacant_seats:
                for candidate in candidates[:]:
                    candidates.remove(candidate)
                    winners.append(candidate['candidate'])
                remaining_vacant_seats = 0
                return

            if candidate['transfer_value'] > quota:
                someone_surpasses_quota = True
                winners.append(candidate['candidate'])
                remaining_vacant_seats -= 1
                candidates.remove(candidate)
                # list of votes to share
                # all the ballots that have this candidate as first option,
                # except for those that only have one option selected
                votes_to_share = self.get_votes_to_share(
                    ballots,
                    candidate['candidate'])
                rest_to_share = candidate['transfer_value'] - quota
                # transfer rest value to second candidates
                for second_candidate in candidates:
                    # number of times the second candidate appears as second
                    # in votes_to_share
                    times_appearing_second = self.ocurrence_second_candidate(
                        votes_to_share,
                        second_candidate['candidate'])
                    increased_value = \
                        rest_to_share * \
                        times_appearing_second * \
                        len(votes_to_share)
                    second_candidate['transfer_value'] += increased_value
                # remove all occurences of the candidate in the ballots
                self.remove_option_from_ballots(ballots, candidate['candidate'])

        # if no candidate surpasses the quota, do an elimination round
        if not someone_surpasses_quota:
            # get last candidate, removing it from the list of candidates
            last_candidate = candidates.pop()
            votes_to_share = self.get_votes_to_share(
                ballots,
                last_candidate['candidate'])
            last_cand_transfer_value = last_candidate['transfer_value']
            # transfer value to second candidates
            for second_candidate in candidates:
                # number of times the second candidate appears as second
                # in votes_to_share
                times_appearing_second = self.ocurrence_second_candidate(
                    votes_to_share,
                    second_candidate['candidate'])
                increased_value = \
                    last_cand_transfer_value * \
                    times_appearing_second * \
                    len(votes_to_share)
                second_candidate['transfer_value'] += increased_value
            # remove all occurences of the candidate in the ballots
            self.remove_option_from_ballots(ballots, last_candidate['candidate'])

    def stv_tally(self, question, ballots):
        voters_by_position = [0] * question['max']
        for answer in question['answers']:
            answer['total_count'] = 0
            answer['winner_position'] = None

        #set total votes
        question['totals']['valid_votes'] = len(ballots)

        # list of winners
        winners = []

        # number of vacant seats for winners
        # this variable will change each time a winner is added to 
        # the winners list
        remaining_vacant_seats = question['num_winners']

        # list of candidates that, at this time, are not on either the winners
        # or the losers list yet
        candidates = [
            dict(
              candidate=index,
              transfer_value=0.0
             )
            for index in
            range(len(question['answers'))]

        # quota
        quota = (len(ballots) + 1) / (question['num_winners'] + 1)

        # round
        round_count = 0
        
        # fill first transfer value with the times each candidate 
        # appears as the first option
        for ballot in ballots:
          candidates[ballot[0]]['transfer_value'] += 1.0


        continue_round = True
        while continue_round:
          # increase round count
          round_count += 1
          # order candidates by increasing name and decreasing transfer value
          candidates = sorted(
              candidates,
              key = lambda x: question['answers'][x['candidate']]['text'])
          candidates = sorted(
              candidates,
              key = lambda x: x['transfer_value'],
              reverse = True)
          self.perform_round(
              question,
              ballots,
              winners,
              losers,
              remaining_vacant_seats,
              candidates,
              quota,
              round_count,
              continue_round)

        for winner_pos, winner in enumerate(winners):
            question['answers'][winner]['winner_position'] = winner_pos

    def perform_tally(self, questions):
        self.report = {}
        report = self.report
        question = questions[self.question_num]
        self.stv_tally(question, self.ballots)

    def post_tally(self, questions):
        '''
        '''
        self.perform_tally(questions)

    def get_log(self):
        '''
        Returns the tally log. Called after post_tally()
        '''
        return self.report
