from random import uniform as rand
from time import time as curr_time

MAX_PLAYER, MIN_PLAYER = 0, 1
MAX_VAL = 1e9
END_VAL = (-MAX_VAL, MAX_VAL)
BIT_COUNT = [0] * 65536
BIT_POS = [[]] * 65536
for i in range(1, 65536):
    BIT_COUNT[i] = BIT_COUNT[i >> 1] + (i & 1)
    BIT_POS[i] = [x + 1 for x in BIT_POS[i >> 1]]
    if i & 1:
        BIT_POS[i].append(0)
BIT_NO = [1 << x for x in range(64)]
NEG_BIT = [x ^ 0xffffffffffffffff for x in BIT_NO]
PROMOTE = ({0, 1, 2, 3, 4, 5, 6, 7}, {56, 57, 58, 59, 60, 61, 62, 63})
MOVE_MAP = [(r, c) for r in range(0, 8) for c in range(0, 8)]
MAX_TIME = 2.7
KW = 750
MW = 500
DW = 1
CW = 1.5
LW = (7, 4, 2, 0, 2, 4, 6)
ELW = (0, 1, 2, 3, 4, 5, 6)


class TreeNode:
    __slots__ = ('board', 'val', 'children', 'move', 'visit', 'expand')

    def resolve_move(self):
        move = self.move
        if len(move) == 2:
            return [MOVE_MAP[move[0]], MOVE_MAP[move[1]]]
        else:
            bit_position = BIT_POS
            caught_bit = ~move[2] & 0xffffffffffffffff
            caught_pos = set(bit_position[caught_bit & 0xffff])
            caught_pos.update(
                x + 16 for x in bit_position[(caught_bit >> 16) & 0xffff])
            caught_pos.update(
                x + 32 for x in bit_position[(caught_bit >> 32) & 0xffff])
            caught_pos.update(
                x + 48 for x in bit_position[(caught_bit >> 48) & 0xffff])
            current_move = move[0]
            result = [MOVE_MAP[current_move]]
            while caught_pos:
                if (current_move + 7) in caught_pos:
                    current_move += 14
                    result.append(MOVE_MAP[current_move])
                    caught_pos.remove(current_move - 7)
                elif (current_move + 9) in caught_pos:
                    current_move += 18
                    result.append(MOVE_MAP[current_move])
                    caught_pos.remove(current_move - 9)
                elif (current_move - 7) in caught_pos:
                    current_move -= 14
                    result.append(MOVE_MAP[current_move])
                    caught_pos.remove(current_move + 7)
                elif (current_move - 9) in caught_pos:
                    current_move -= 18
                    result.append(MOVE_MAP[current_move])
                    caught_pos.remove(current_move + 9)
            return result

    def __init__(self, board, move=None):
        self.board = board
        self.val = END_VAL[board.player]
        self.move = move
        self.visit = self.min_visit if board.player else self.max_visit
        self.expand = self.expand_func

    def expand_func(self):
        board = self.board
        moves = board.generate_move()
        self.children = [TreeNode(board.make_move(x), x) for x in moves]
        self.expand = lambda: None

    def max_visit(self, depth, alpha, beta, start_time):
        ct = curr_time
        mt = MAX_TIME
        if ct() - start_time >= mt:
            return
        if depth <= 0 and self.board.is_stable:
            self.val = self.board.eval()
        else:
            self.expand()
            children = self.children
            for child in children:
                child.visit(depth - 1, alpha, beta, start_time)
                if ct() - start_time >= mt:
                    return
                alpha = max(alpha, child.val)
                if beta <= alpha:
                    break
            if ct() - start_time < mt:
                children.sort(key=lambda x: x.val, reverse=True)
            self.val = alpha

    def min_visit(self, depth, alpha, beta, start_time):
        ct = curr_time
        mt = MAX_TIME
        if ct() - start_time >= mt:
            return
        if depth <= 0 and self.board.is_stable:
            self.val = self.board.eval()
        else:
            self.expand()
            children = self.children
            for child in children:
                child.visit(depth - 1, alpha, beta, start_time)
                if ct() - start_time >= mt:
                    return
                beta = min(beta, child.val)
                if beta <= alpha:
                    break
            if ct() - start_time < mt:
                children.sort(key=lambda x: x.val)
            self.val = beta


class Board:
    __slots__ = ('boards', 'player', 'jump_func', 'mover_func', 'not_endgame', 'is_stable')

    @staticmethod
    def count_bit(number, table):
        return table[number & 0xffff] + table[(number >> 16) & 0xffff] + table[(number >> 32) & 0xffff] + table[(number >> 48) & 0xffff]

    def __init__(self, player, boards):
        self.boards = boards
        self.player = player
        if player:
            self.not_endgame = self.can_black_move
            self.mover_func = self.find_black_moves
            self.jump_func = self.find_black_jumps
            pieces = boards[1]
            enemies = boards[0]
            kings = boards[2] & pieces
            noc = ~(pieces | enemies) & 0xffffffffffffffff
            enemies &= 0x007e7e7e7e7e7e00
            self.is_stable = not (enemies & (((noc >> 7) & (pieces << 7)) |
                                             ((noc >> 9) & (pieces << 9)) |
                                             ((noc << 9) & (kings >> 9)) |
                                             ((noc << 7) & (kings >> 7))))
        else:
            self.not_endgame = self.can_red_move
            self.mover_func = self.find_red_moves
            self.jump_func = self.find_red_jumps
            pieces = boards[0]
            enemies = boards[1]
            kings = boards[2] & pieces
            noc = ~(pieces | enemies) & 0xffffffffffffffff
            enemies &= 0x007e7e7e7e7e7e00
            self.is_stable = not (enemies & (((noc >> 7) & (kings << 7)) |
                                             ((noc >> 9) & (kings << 9)) |
                                             ((noc << 9) & (pieces >> 9)) |
                                             ((noc << 7) & (pieces >> 7))))

    def can_black_move(self):
        pieces = self.boards[1]
        red_board = self.boards[0]
        not_occupied = ~(pieces | red_board) & 0xffffffffffffffff
        kings = self.boards[2] & pieces
        movers = (not_occupied >> 9) & (pieces & 0x007f7f7f7f7f7f7f)
        if movers:
            return True
        movers = (not_occupied >> 7) & (pieces & 0x00fefefefefefefe)
        if movers:
            return True
        if kings:
            movers = (not_occupied << 7) & (kings & 0x7f7f7f7f7f7f7f00)
            if movers:
                return True
            movers = (not_occupied << 9) & (kings & 0xfefefefefefefe00)
            if movers:
                return True
        movers = ((((not_occupied & 0x3f3f3f3f3f3f0000) >> 7) & red_board) >> 7) & pieces
        if movers:
            return True
        movers = ((((not_occupied & 0xfcfcfcfcfcfc0000) >> 9) & red_board) >> 9) & pieces
        if movers:
            return True
        if kings:
            movers = ((((not_occupied & 0x0000fcfcfcfcfcfc) << 7) & red_board) << 7) & kings
            if movers:
                return True
            movers = ((((not_occupied & 0x00003f3f3f3f3f3f) << 9) & red_board) << 9) & kings
            if movers:
                return True
        return False

    def can_red_move(self):
        pieces = self.boards[0]
        black_board = self.boards[1]
        not_occupied = ~(pieces | black_board) & 0xffffffffffffffff
        kings = self.boards[2] & pieces
        movers = (not_occupied << 7) & (pieces & 0x7f7f7f7f7f7f7f00)
        if movers:
            return True
        movers = (not_occupied << 9) & (pieces & 0xfefefefefefefe00)
        if movers:
            return True
        if kings:
            movers = (not_occupied >> 9) & (kings & 0x007f7f7f7f7f7f7f)
            if movers:
                return True
            movers = (not_occupied >> 7) & (kings & 0x00fefefefefefefe)
            if movers:
                return True
        movers = ((((not_occupied & 0x0000fcfcfcfcfcfc) << 7) & black_board) << 7) & pieces
        if movers:
            return True
        movers = ((((not_occupied & 0x00003f3f3f3f3f3f) << 9) & black_board) << 9) & pieces
        if movers:
            return True
        if kings:
            movers = ((((not_occupied & 0x3f3f3f3f3f3f0000) >> 7) & black_board) >> 7) & kings
            if movers:
                return True
            movers = ((((not_occupied & 0xfcfcfcfcfcfc0000) >> 9) & black_board) >> 9) & kings
            if movers:
                return True
        return False

    @staticmethod
    def add_move(movers, a, ef, bp):
        i = 0
        while movers:
            ef((x + i, x + i + a) for x in bp[movers & 0xffff])
            movers >>= 16
            i += 16

    def find_red_moves(self):
        add_move = Board.add_move
        result = []
        extend_result = result.extend
        bit_position = BIT_POS
        pieces = self.boards[0]
        not_occupied = ~(pieces | self.boards[1]) & 0xffffffffffffffff
        kings = self.boards[2] & pieces
        movers = (not_occupied << 7) & (pieces & 0x7f7f7f7f7f7f7f00)
        if movers:
            add_move(movers, -7, extend_result, bit_position)
        movers = (not_occupied << 9) & (pieces & 0xfefefefefefefe00)
        if movers:
            add_move(movers, -9, extend_result, bit_position)
        if kings:
            movers = (not_occupied >> 9) & (kings & 0x007f7f7f7f7f7f7f)
            if movers:
                add_move(movers, 9, extend_result, bit_position)
            movers = (not_occupied >> 7) & (kings & 0x00fefefefefefefe)
            if movers:
                add_move(movers, 7, extend_result, bit_position)
        return result

    @staticmethod
    def add_jump(jumpers, a, ej, ng, bp):
        i = 0
        while jumpers:
            ia = i + a
            ia2 = i + (a >> 1)
            ej((x + i, x + ia, ng[x + ia2]) for x in bp[jumpers & 0xffff])
            jumpers >>= 16
            i += 16

    def find_red_jumps(self):
        add_jump = Board.add_jump
        bit_position = BIT_POS
        neg_bit = NEG_BIT
        jump_moves = []
        extend_jump = jump_moves.extend
        result = []
        pieces = self.boards[0]
        black_board = self.boards[1]
        not_occupied = ~(pieces | black_board) & 0xffffffffffffffff
        kings = self.boards[2] & pieces
        jumpers = ((((not_occupied & 0x0000fcfcfcfcfcfc) << 7)
                    & black_board) << 7) & pieces
        if jumpers:
            add_jump(jumpers, -14, extend_jump, neg_bit, bit_position)
        jumpers = ((((not_occupied & 0x00003f3f3f3f3f3f) << 9)
                    & black_board) << 9) & pieces
        if jumpers:
            add_jump(jumpers, -18, extend_jump, neg_bit, bit_position)
        if kings:
            jumpers = ((((not_occupied & 0xfcfcfcfcfcfc0000) >> 9)
                        & black_board) >> 9) & kings
            if jumpers:
                add_jump(jumpers, 18, extend_jump, neg_bit, bit_position)
            jumpers = ((((not_occupied & 0x3f3f3f3f3f3f0000) >> 7)
                        & black_board) >> 7) & kings
            if jumpers:
                add_jump(jumpers, 14, extend_jump, neg_bit, bit_position)

        if jump_moves:
            local_sq = BIT_NO
            local_pieces = pieces
            local_black_board = black_board
            append_stack = jump_moves.append
            stack_pop = jump_moves.pop
            while jump_moves:
                jump_step = stack_pop()
                first = jump_step[0]
                last = jump_step[1]
                caught = jump_step[2]
                stack_len = len(jump_moves)
                piece = local_sq[last]
                temp_black_board = local_black_board & caught
                curr_not_occupied = ~((local_pieces | temp_black_board | local_sq[
                    last]) ^ local_sq[first]) & 0xffffffffffffffff
                if kings & local_sq[first]:
                    if (piece & 0x0000fcfcfcfcfcfc) and (local_sq[last + 14] & curr_not_occupied) and (local_sq[last + 7] & temp_black_board):
                        append_stack(
                            (first, last + 14, caught ^ local_sq[last + 7]))
                    if (piece & 0x00003f3f3f3f3f3f) and (local_sq[last + 18] & curr_not_occupied) and (local_sq[last + 9] & temp_black_board):
                        append_stack(
                            (first, last + 18, caught ^ local_sq[last + 9]))
                if (piece & 0x3f3f3f3f3f3f0000) and (local_sq[last - 14] & curr_not_occupied) and (local_sq[last - 7] & temp_black_board):
                    append_stack(
                        (first, last - 14, caught ^ local_sq[last - 7]))
                if (piece & 0xfcfcfcfcfcfc0000) and (local_sq[last - 18] & curr_not_occupied) and (local_sq[last - 9] & temp_black_board):
                    append_stack(
                        (first, last - 18, caught ^ local_sq[last - 9]))
                if stack_len == len(jump_moves):
                    result.append(jump_step)
        return result

    def find_black_moves(self):
        add_move = Board.add_move
        bit_position = BIT_POS
        result = []
        extend_result = result.extend
        pieces = self.boards[1]
        not_occupied = ~(pieces | self.boards[0]) & 0xffffffffffffffff
        kings = self.boards[2] & pieces
        movers = (not_occupied >> 9) & (pieces & 0x007f7f7f7f7f7f7f)
        if movers:
            add_move(movers, 9, extend_result, bit_position)
        movers = (not_occupied >> 7) & (pieces & 0x00fefefefefefefe)
        if movers:
            add_move(movers, 7, extend_result, bit_position)
        if kings:
            movers = (not_occupied << 7) & (kings & 0x7f7f7f7f7f7f7f00)
            if movers:
                add_move(movers, -7, extend_result, bit_position)
            movers = (not_occupied << 9) & (kings & 0xfefefefefefefe00)
            if movers:
                add_move(movers, -9, extend_result, bit_position)
        return result

    def find_black_jumps(self):
        add_jump = Board.add_jump
        neg_bit = NEG_BIT
        bit_position = BIT_POS
        jump_moves = []
        result = []
        pieces = self.boards[1]
        extend_jump = jump_moves.extend
        red_board = self.boards[0]
        not_occupied = ~(pieces | red_board) & 0xffffffffffffffff
        kings = self.boards[2] & pieces
        jumpers = ((((not_occupied & 0x3f3f3f3f3f3f0000) >> 7)
                    & red_board) >> 7) & pieces
        if jumpers:
            add_jump(jumpers, 14, extend_jump, neg_bit, bit_position)
        jumpers = ((((not_occupied & 0xfcfcfcfcfcfc0000) >> 9)
                    & red_board) >> 9) & pieces
        if jumpers:
            add_jump(jumpers, 18, extend_jump, neg_bit, bit_position)
        if kings:
            jumpers = ((((not_occupied & 0x00003f3f3f3f3f3f) << 9)
                        & red_board) << 9) & kings
            if jumpers:
                add_jump(jumpers, -18, extend_jump, neg_bit, bit_position)
            jumpers = ((((not_occupied & 0x0000fcfcfcfcfcfc) << 7)
                        & red_board) << 7) & kings
            if jumpers:
                add_jump(jumpers, -14, extend_jump, neg_bit, bit_position)

        if jump_moves:
            local_sq = BIT_NO
            local_pieces = pieces
            local_red_board = red_board
            append_stack = jump_moves.append
            stack_pop = jump_moves.pop
            while jump_moves:
                jump_step = stack_pop()
                first = jump_step[0]
                last = jump_step[1]
                caught = jump_step[2]
                stack_len = len(jump_moves)
                piece = local_sq[last]
                temp_red_board = local_red_board & caught
                curr_not_occupied = ~((local_pieces | temp_red_board | local_sq[
                    last]) ^ local_sq[first]) & 0xffffffffffffffff
                if kings & local_sq[first]:
                    if (piece & 0x3f3f3f3f3f3f0000) and (local_sq[last - 14] & curr_not_occupied) and (local_sq[last - 7] & temp_red_board):
                        append_stack(
                            (first, last - 14, caught ^ local_sq[last - 7]))
                    if (piece & 0xfcfcfcfcfcfc0000) and (local_sq[last - 18] & curr_not_occupied) and (local_sq[last - 9] & temp_red_board):
                        append_stack(
                            (first, last - 18, caught ^ local_sq[last - 9]))
                if (piece & 0x0000fcfcfcfcfcfc) and (local_sq[last + 14] & curr_not_occupied) and (local_sq[last + 7] & temp_red_board):
                    append_stack(
                        (first, last + 14, caught ^ local_sq[last + 7]))
                if (piece & 0x00003f3f3f3f3f3f) and (local_sq[last + 18] & curr_not_occupied) and (local_sq[last + 9] & temp_red_board):
                    append_stack(
                        (first, last + 18, caught ^ local_sq[last + 9]))
                if stack_len == len(jump_moves):
                    result.append(jump_step)
        return result

    def generate_move(self):
        result = self.jump_func()
        if not result:
            result = self.mover_func()
        return result

    def make_move(self, move):
        first = BIT_NO[move[0]]
        last = BIT_NO[move[1]]
        player_board = self.boards[self.player]
        player_board ^= first
        player_board |= last
        king_board = self.boards[2]
        if king_board & first:
            king_board ^= first
            king_board |= last
        elif move[1] in PROMOTE[self.player]:
            king_board |= last
        enemy = self.player ^ 1
        enemy_board = self.boards[enemy]
        if len(move) == 3:
            enemy_board &= move[2]
            king_board &= move[2]
        boards = (enemy_board, player_board, king_board) if self.player else (player_board, enemy_board, king_board)
        return Board(enemy, boards)

    def eval(self):
        if self.not_endgame():
            kw = KW
            mw = MW
            dw = DW
            cw = CW

            cb = Board.count_bit
            bct = BIT_COUNT
            ak = self.boards[2]
            bp = self.boards[1]
            bk = bp & ak
            bm = bp ^ bk
            rp = self.boards[0]
            rk = rp & ak
            rm = rk ^ rp
            ap = bp | rp
            ca = cb(ap, bct)
            if ca > 12:
                lw = LW
            else:
                lw = ELW

            bv = 0
            if bk:
                bv += kw * cb(bk, bct)

            if bm:
                bv += mw * cb(bm, bct)  # men weight
                cm = bm & 0xff818181818181ff
                bv += cw * cb(cm, bct)
                ncm = bm & 0x007e7e7e7e7e7e00
                defense = ncm & (bp << 9)
                bv += dw * cb(defense, bct)
                defense = ncm & (bp << 7)
                bv += dw * cb(defense, bct)
                idx = 0
                temp = bm & 0x00ffffffffffffff
                while temp:
                    bv += lw[idx] * bct[temp & 0xff]
                    temp >>= 8
                    idx += 1
            rv = 0
            if rk:
                rv += kw * cb(rk, bct)
            if rm:
                rv += mw * cb(rm, bct)
                cm = rm & 0xff818181818181ff
                rv += cw * cb(cm, bct)
                ncm = rm & 0x007e7e7e7e7e7e00
                defense = ncm & (rp >> 7)
                rv += dw * cb(defense, bct)
                defense = ncm & (rp >> 9)
                rv += dw * cb(defense, bct)

                idx = 6
                temp = rm >> 8
                while temp:
                    rv += lw[idx] * bct[temp & 0xff]
                    temp >>= 8
                    idx -= 1
            val = rand(0.0, 0.1)
            val += rv - bv
            return val
        else:
            return END_VAL[self.player]


class Player:
    def __init__(self, str_name):
        self.str = str_name
        self.value = 0 if str_name == 'r' else 1
        self.maximize = self.value == MAX_PLAYER

    def __str__(self):
        return self.str

    def board_from_state(self, state):
        red, black, kings = 0, 0, 0
        shift = 1
        for r in range(0, 8):
            for c in range(0, 8):
                if state[r][c] == 'r':
                    red |= shift
                elif state[r][c] == 'b':
                    black |= shift
                elif state[r][c] == 'R':
                    red |= shift
                    kings |= shift
                elif state[r][c] == 'B':
                    black |= shift
                    kings |= shift
                shift <<= 1
        return Board(self.value, (red, black, kings))

    def nextMove(self, state):
        ct = curr_time
        start_time = ct()
        board = self.board_from_state(state)
        root = TreeNode(board)
        curr_depth = 3
        root.expand()
        children = root.children
        best_child = None
        if not children:
            return []
        if len(children) == 1:
            return children[0].resolve_move()
        sort_child = children.sort
        mt = MAX_TIME
        max_val = MAX_VAL
        if self.maximize:
            while ct() - start_time < mt:
                for child in children:
                    child.visit(curr_depth - 1, -max_val, max_val, start_time)
                if ct() - start_time >= mt:
                    break
                sort_child(key=lambda x: x.val, reverse=True)
                best_child = children[0]
                curr_depth += 2
        else:
            while ct() - start_time < mt:
                for child in children:
                    child.visit(curr_depth - 1, -max_val, max_val, start_time)
                if ct() - start_time >= mt:
                    break
                sort_child(key=lambda x: x.val)
                best_child = children[0]
                curr_depth += 2

        if best_child is None:
            return []
        else:
            return best_child.resolve_move()
