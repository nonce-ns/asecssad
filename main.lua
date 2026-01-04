local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 67) then
					if (Enum <= 33) then
						if (Enum <= 16) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum == 0) then
											local A;
											local K;
											local B;
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										else
											local B;
											local A;
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									elseif (Enum == 2) then
										if (Stk[Inst[2]] <= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B;
										local A;
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum == 6) then
									local B;
									local Edx;
									local Results;
									local A;
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum == 8) then
										do
											return Stk[Inst[2]]();
										end
									else
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									end
								elseif (Enum == 10) then
									do
										return Stk[Inst[2]];
									end
								else
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 14) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 15) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 24) then
							if (Enum <= 20) then
								if (Enum <= 18) then
									if (Enum > 17) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										local Results, Limit = _R(Stk[A]());
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum == 19) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 22) then
								if (Enum == 21) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum == 23) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 28) then
							if (Enum <= 26) then
								if (Enum == 25) then
									Stk[Inst[2]] = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum > 27) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 30) then
							if (Enum == 29) then
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 31) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 32) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							do
								return;
							end
						end
					elseif (Enum <= 50) then
						if (Enum <= 41) then
							if (Enum <= 37) then
								if (Enum <= 35) then
									if (Enum > 34) then
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									else
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum == 36) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 39) then
								if (Enum > 38) then
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local Edx;
									local Results;
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 40) then
								local K;
								local B;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 45) then
							if (Enum <= 43) then
								if (Enum == 42) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
								else
									local NewProto = Proto[Inst[3]];
									local NewUvals;
									local Indexes = {};
									NewUvals = Setmetatable({}, {__index=function(_, Key)
										local Val = Indexes[Key];
										return Val[1][Val[2]];
									end,__newindex=function(_, Key, Value)
										local Val = Indexes[Key];
										Val[1][Val[2]] = Value;
									end});
									for Idx = 1, Inst[4] do
										VIP = VIP + 1;
										local Mvm = Instr[VIP];
										if (Mvm[1] == 108) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum > 44) then
								local Edx;
								local Results, Limit;
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A], Stk[A + 1];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 47) then
							if (Enum == 46) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 48) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
						elseif (Enum == 49) then
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A = Inst[2];
							local Results = {Stk[A]()};
							local Limit = Inst[4];
							local Edx = 0;
							for Idx = A, Limit do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 58) then
						if (Enum <= 54) then
							if (Enum <= 52) then
								if (Enum > 51) then
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								else
									local B;
									local T;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum > 53) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 56) then
							if (Enum > 55) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 57) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 62) then
						if (Enum <= 60) then
							if (Enum > 59) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum == 61) then
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Top));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 64) then
						if (Enum == 63) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 65) then
						VIP = Inst[3];
					elseif (Enum == 66) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						local B;
						local A;
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 101) then
					if (Enum <= 84) then
						if (Enum <= 75) then
							if (Enum <= 71) then
								if (Enum <= 69) then
									if (Enum == 68) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										Stk[Inst[2]] = Inst[3] ~= 0;
									end
								elseif (Enum > 70) then
									Stk[Inst[2]]();
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 73) then
								if (Enum == 72) then
									local A = Inst[2];
									local Cls = {};
									for Idx = 1, #Lupvals do
										local List = Lupvals[Idx];
										for Idz = 0, #List do
											local Upv = List[Idz];
											local NStk = Upv[1];
											local DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
								else
									local K;
									local B;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum > 74) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 79) then
							if (Enum <= 77) then
								if (Enum > 76) then
									Stk[Inst[2]] = #Stk[Inst[3]];
								else
									local K;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum > 78) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local K;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 81) then
							if (Enum > 80) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 82) then
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						elseif (Enum > 83) then
							Stk[Inst[2]] = {};
						else
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 92) then
						if (Enum <= 88) then
							if (Enum <= 86) then
								if (Enum > 85) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum == 87) then
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 90) then
							if (Enum > 89) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum > 91) then
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 96) then
						if (Enum <= 94) then
							if (Enum == 93) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Top));
								end
							end
						elseif (Enum == 95) then
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 98) then
						if (Enum == 97) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 99) then
						local A = Inst[2];
						local T = Stk[A];
						for Idx = A + 1, Inst[3] do
							Insert(T, Stk[Idx]);
						end
					elseif (Enum == 100) then
						local B;
						local Edx;
						local Results;
						local A;
						A = Inst[2];
						Results = {Stk[A](Stk[A + 1])};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 118) then
					if (Enum <= 109) then
						if (Enum <= 105) then
							if (Enum <= 103) then
								if (Enum == 102) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum > 104) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local Results;
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 107) then
							if (Enum > 106) then
								Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Stk[A], Stk[A + 1];
								end
							end
						elseif (Enum == 108) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 113) then
						if (Enum <= 111) then
							if (Enum == 110) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A]();
							end
						elseif (Enum > 112) then
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 115) then
						if (Enum > 114) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 116) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Enum == 117) then
						local Edx;
						local Results, Limit;
						local B;
						local A;
						A = Inst[2];
						Stk[A] = Stk[A]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return Stk[Inst[2]];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						local A = Inst[2];
						local C = Inst[4];
						local CB = A + 2;
						local Result = {Stk[A](Stk[A + 1], Stk[CB])};
						for Idx = 1, C do
							Stk[CB + Idx] = Result[Idx];
						end
						local R = Result[1];
						if R then
							Stk[CB] = R;
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					end
				elseif (Enum <= 127) then
					if (Enum <= 122) then
						if (Enum <= 120) then
							if (Enum == 119) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum == 121) then
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 124) then
						if (Enum == 123) then
							local Edx;
							local Results, Limit;
							local B;
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 125) then
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					elseif (Enum > 126) then
						local K;
						local B;
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						local B;
						local A;
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 131) then
					if (Enum <= 129) then
						if (Enum > 128) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum == 130) then
						local Results;
						local K;
						local B;
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A]());
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Stk[A + 1])};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 133) then
					if (Enum == 132) then
						local K;
						local B;
						local A;
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						Upvalues[Inst[3]] = Stk[Inst[2]];
					end
				elseif (Enum <= 134) then
					if not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum == 135) then
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
				else
					local B = Inst[3];
					local K = Stk[B];
					for Idx = B + 1, Inst[4] do
						K = K .. Stk[Idx];
					end
					Stk[Inst[2]] = K;
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!5C3Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C61796572030B3Q00482Q74705365727669636503183Q00682Q74703A2Q2F3139322E3136382E312E373A383Q302F03083Q00546865466F72676503063Q00436F6E666967030F3Q002F436F6E6669674E616D652E74787403053Q007072696E7403193Q005B54686520466F7267655D204C6F6164696E672055493Q2E03023Q005F4703053Q00466F72676503073Q004261736555524C03053Q007063612Q6C030A3Q006C6F6164737472696E6703073Q00482Q7470476574031C3Q00682Q7470733A2Q2F7369726975732E6D656E752F7261796669656C64030C3Q0043726561746557696E646F7703043Q004E616D65030E3Q0054686520466F7267652076332E32030C3Q004C6F6164696E675469746C6503093Q0054686520466F726765030F3Q004C6F6164696E675375627469746C6503123Q004C6F6164696E67206D6F64756C65733Q2E03133Q00436F6E66696775726174696F6E536176696E6703073Q00456E61626C65642Q01030A3Q00466F6C6465724E616D6503083Q0046696C654E616D6503093Q004B657953797374656D010003093Q0043726561746554616203043Q004661726D022Q00A0E9AAB3F04103083Q004175746F53652Q6C03063Q004D696E696E6703083Q0054656C65706F72742Q033Q00466C792Q033Q0046505303063Q00506C6179657203083Q0053652Q74696E677303063Q0057696E646F7703083Q005261796669656C6403043Q005461627303053Q005574696C7303073Q00476574522Q6F74030C3Q00476574436C65616E4E616D6503073Q00436C65616E7570030B3Q00436F2Q6E656374696F6E73030D3Q0043726561746553656374696F6E030E3Q0053637269707420436F6E74726F6C030C3Q0043726561746542752Q746F6E030D3Q00556E6C6F61642053637269707403083Q0043612Q6C6261636B03153Q00466F72636520436C65616E7570205068797369637303043Q00496E666F030B3Q004372656174654C6162656C03123Q004175746F204661726D2026204D696E696E67030C3Q0044656275672026204C6F6773030C3Q00437265617465546F2Q676C65030F3Q0053686F77204C6F672057696E646F77030C3Q0043752Q72656E7456616C756503043Q00466C6167030D3Q0053686F774C6F6757696E646F77030E3Q005265736574202620436F6E66696703183Q00526573657420412Q6C202620436C65617220436F6E666967030B3Q00437265617465496E707574030B3Q00436F6E666967204E616D65030F3Q00506C616365686F6C64657254657874030B3Q00436F6E666967206E616D6503183Q0052656D6F7665546578744166746572466F6375734C6F7374030B3Q005361766520436F6E666967030B3Q004C6F616420436F6E66696703043Q006661726D03063Q006D696E696E6703083Q0074656C65706F72742Q033Q006574632Q033Q0066707303063Q00706C61796572030C3Q0063616D6572615F7368616B6503043Q0073652Q6C030D3Q00726567696F6E5F627970612Q7303043Q007461736B03053Q00737061776E03063Q004E6F7469667903053Q005469746C6503073Q00436F6E74656E74031D3Q005549205265616479202D204C6F6164696E67206D6F64756C65733Q2E03083Q004475726174696F6E026Q000840031E3Q005B54686520466F7267655D204D61696E206C6F6164657220726561647921001F012Q00121D3Q00013Q00206Q000200122Q000200038Q0002000200202Q00013Q000400122Q000200013Q00202Q00020002000200122Q000400056Q00020004000200122Q000300063Q001219000400073Q001219000500084Q006C000600043Q001219000700094Q008800060006000700023F00075Q00062B00080001000100022Q006C3Q00074Q006C3Q00053Q00062B00090002000100032Q006C3Q00064Q006C3Q00084Q006C3Q00053Q00062B000A0003000100032Q006C3Q00044Q006C3Q00084Q006C3Q00064Q000F000B00096Q000B000100024Q000C000B3Q00122Q000D000A3Q00122Q000E000B6Q000D0002000100122Q000D000C3Q00202Q000D000D000D00062Q000D0028000100010004413Q00280001001204000D000C4Q0054000E5Q001009000D000D000E001204000D000C3Q002087000D000D000D001009000D000E000300023F000D00043Q001204000E000F3Q00062B000F0005000100012Q006C3Q00034Q007B000E0002000100122Q000E000A3Q00122Q000F000B6Q000E0002000100122Q000E00103Q00122Q000F00013Q00202Q000F000F001100122Q001100126Q000F00116Q000E3Q00022Q006F000E00010002002044000F000E00134Q00113Q000500302Q00110014001500302Q00110016001700302Q0011001800194Q00123Q000300302Q0012001B001C00102Q0012001D000400102Q0012001E000B00102Q0011001A0012002Q300011001F00202Q0003000F0011000200202Q0010000F002100122Q001200223Q00122Q001300236Q00100013000200202Q0011000F002100122Q001300243Q00122Q001400236Q00110014000200202Q0012000F0021001227001400253Q00122Q001500236Q00120015000200202Q0013000F002100122Q001500263Q00122Q001600236Q00130016000200202Q0014000F002100122Q001600273Q00122Q001700234Q000300140017000200202Q0015000F002100122Q001700283Q00122Q001800236Q00150018000200202Q0016000F002100122Q001800293Q00122Q001900236Q00160019000200202Q0017000F00210012190019002A3Q001219001A00234Q000D0017001A000200023F001800063Q00023F001900073Q001204001A000C3Q002087001A001A000D000686001A006F000100010004413Q006F0001001204001A000C4Q0054001B5Q001009001A000D001B001204001A000C3Q002013001A001A000D00102Q001A002B000F00122Q001A000C3Q00202Q001A001A000D00102Q001A002C000E001271001A000C3Q00202Q001A001A000D4Q001B3Q000800102Q001B0022001000102Q001B0024001100102Q001B0025001200102Q001B0026001300102Q001B0027001400102Q001B0028001500102Q001B00290016001009001B002A0017001046001A002D001B00122Q001A000C3Q00202Q001A001A000D4Q001B3Q000200102Q001B002F001800102Q001B0030001900102Q001A002E001B00122Q001A000C3Q00202Q001A001A000D00202Q001A001A0031000686001A0090000100010004413Q00900001001204001A000C3Q002087001A001A000D2Q0054001B5Q001009001A0031001B001204001A000C3Q002087001A001A000D002087001A001A0032000686001A0099000100010004413Q00990001001204001A000C3Q002087001A001A000D2Q0054001B5Q001009001A0032001B001204001A000C3Q00203C001A001A000D00102Q001A000E000300202Q001A0017003300122Q001C00346Q001A001C000200202Q001B001700354Q001D3Q000200302Q001D0014003600062B001E0008000100022Q006C3Q000D4Q006C3Q000E3Q001017001D0037001E4Q001B001D000100202Q001B001700354Q001D3Q000200302Q001D0014003800062B001E0009000100022Q006C3Q000D4Q006C3Q000E3Q001070001D0037001E4Q001B001D000100202Q001B0017003300122Q001D00396Q001B001D000200202Q001C0017003A00122Q001E00156Q001C001E000100202Q001C0017003A00122Q001E003B4Q0074001C001E000100204B001C0017003300122Q001E003C6Q001C001E000200202Q001D0017003D4Q001F3Q000400302Q001F0014003E00302Q001F003F002000302Q001F0040004100023F0020000A3Q001061001F003700204Q001D001F000100202Q001D0017003300122Q001F00426Q001D001F000200202Q001E001700354Q00203Q000200302Q00200014004300062B0021000B000100022Q006C3Q000D4Q006C3Q000E3Q0010090020003700212Q0074001E0020000100023F001E000C3Q00023F001F000D3Q00062B0020000E000100032Q006C3Q00084Q006C3Q000C4Q006C3Q00043Q00062B0021000F000100022Q006C3Q000E4Q006C3Q001E3Q00062B00220010000100042Q006C3Q00044Q006C3Q00214Q006C3Q00204Q006C3Q00023Q00062B00230011000100032Q006C3Q00024Q006C3Q000E4Q006C3Q001F4Q002900245Q00202Q0025001700444Q00273Q000500302Q00270014004500102Q0027003F000C00302Q00270046004700302Q00270048002000062B00280012000100052Q006C3Q00244Q006C3Q00084Q006C3Q000C4Q006C3Q000A4Q006C3Q000E3Q00107E0027003700284Q00250027000200202Q0026001700354Q00283Q000200302Q00280014004900062B00290013000100032Q006C3Q00224Q006C3Q000E4Q006C3Q00203Q0010170028003700294Q00260028000100202Q0026001700354Q00283Q000200302Q00280014004A00062B00290014000100032Q006C3Q00204Q006C3Q00234Q006C3Q000E3Q0010650028003700294Q0026002800014Q002600093Q00122Q0027004B3Q00122Q0028004C3Q00122Q0029004D3Q00122Q002A004E3Q00122Q002B004F3Q001233002C00503Q00122Q002D00513Q00122Q002E00523Q00122Q002F00536Q00260009000100062B00270015000100012Q006C3Q00033Q001204002800543Q00208700280028005500062B00290016000100032Q006C3Q00264Q006C3Q00274Q006C3Q000E4Q00810028000200010020530028000E00564Q002A3Q000300302Q002A0057001500302Q002A0058005900302Q002A005A005B4Q0028002A000100122Q0028000A3Q00122Q0029005C6Q0028000200016Q00013Q00173Q00053Q0003083Q00746F737472696E67034Q0003043Q0067737562030C3Q005E25732A282E2D2925732A2403023Q002531010B3Q001204000100013Q0006570002000400013Q0004413Q00040001001219000200024Q005800010002000200200500010001000300122Q000300043Q00122Q000400056Q000100046Q00019Q0000017Q00043Q00034Q0003043Q006773756203093Q005B5E2577252D255F5D03013Q005F01114Q002A00016Q006C00026Q005800010002000200261000010007000100010004413Q000700012Q002A000200014Q000A000200023Q002042000200010002001219000400033Q001219000500044Q000D0002000500020026100002000F000100010004413Q000F00012Q002A000300014Q000A000300024Q000A000200024Q00203Q00017Q00033Q0003063Q00697366696C6503053Q007063612Q6C03083Q007265616466696C6500173Q0012043Q00013Q0006733Q001400013Q0004413Q001400010012043Q00014Q002A00016Q00583Q000200020006733Q001400013Q0004413Q001400010012043Q00023Q001204000100034Q002A00026Q003B3Q000200010006733Q001400013Q0004413Q001400010006730001001400013Q0004413Q001400012Q002A000200014Q006C000300014Q004A000200034Q005A00026Q002A3Q00024Q000A3Q00024Q00203Q00017Q00043Q0003093Q00777269746566696C6503183Q0046696C6573797374656D206E6F742073752Q706F7274656403083Q006973666F6C646572030A3Q006D616B65666F6C646572011C3Q001204000100013Q00068600010006000100010004413Q000600012Q004500015Q001219000200024Q006A000100033Q001204000100033Q0006730001001100013Q0004413Q00110001001204000100034Q002A00026Q005800010002000200068600010011000100010004413Q00110001001204000100044Q002A00026Q00810001000200012Q002A000100014Q002C00028Q00010002000200122Q000200016Q000300026Q000400016Q0002000400014Q000200016Q000300016Q000200038Q00017Q000B3Q0003063Q0069706169727303093Q00776F726B7370616365030B3Q004765744368696C6472656E03043Q004E616D65030B3Q004D61676963436172706574030F3Q004661726D4D6167696343617270657403093Q00466C79436172706574030E3Q0054656C65706F727443617270657403113Q004D696E696E674D6167696343617270657403083Q005A6F6E655061727403053Q007063612Q6C001B3Q0012153Q00013Q00122Q000100023Q00202Q0001000100034Q000100029Q00000200044Q0018000100208700050004000400263700050013000100050004413Q0013000100263700050013000100060004413Q0013000100263700050013000100070004413Q0013000100263700050013000100080004413Q0013000100263700050013000100090004413Q00130001002610000500170001000A0004413Q001700010012040006000B3Q00062B00073Q000100012Q006C3Q00044Q00810006000200012Q004800035Q0006763Q0006000100020004413Q000600012Q00203Q00013Q00013Q00013Q0003073Q0044657374726F7900044Q002A7Q0020425Q00012Q00813Q000200012Q00203Q00017Q00043Q0003063Q00697366696C6503083Q006C6F67732E6C756103083Q006C6F616466696C6503053Q007063612Q6C00153Q0012043Q00013Q0006733Q000D00013Q0004413Q000D00010012043Q00013Q001219000100024Q00583Q000200020006733Q000D00013Q0004413Q000D00010012043Q00033Q001219000100024Q00583Q000200022Q00473Q000100010004413Q001400012Q002A7Q0006733Q001400013Q0004413Q001400010012043Q00043Q00062B00013Q000100012Q002A8Q00813Q000200012Q00203Q00013Q00013Q00063Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574030B3Q006C6F67732E6C75613F763D03083Q00746F737472696E6703043Q007469636B000F3Q00124E3Q00013Q00122Q000100023Q00202Q0001000100034Q00035Q00122Q000400043Q00122Q000500053Q00122Q000600066Q000600016Q00053Q00024Q0003000300054Q000400016Q000100049Q0000026Q000100016Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403053Q00546F72736F010C3Q0006520001000A00013Q0004413Q000A000100204200013Q0001001219000300024Q000D0001000300020006860001000A000100010004413Q000A000100204200013Q0001001219000300034Q000D0001000300022Q000A000100024Q00203Q00017Q00053Q0003043Q006773756203043Q0025642B24034Q00030C3Q005E25732A282E2D2925732A2403023Q002531010A3Q00202E00013Q000100122Q000300023Q00122Q000400036Q00010004000200202Q00010001000100122Q000300043Q00122Q000400056Q0001000400024Q000100028Q00017Q00163Q0003053Q007072696E7403183Q005B54686520466F7267655D20556E6C6F6164696E673Q2E03023Q005F4703053Q00466F72676503093Q0052657365744661726D03053Q007063612Q6C030B3Q0052657365744D696E696E67030D3Q00526573657454656C65706F7274030E3Q0052657365744175746F466F726765030F3Q0052657365744175746F53652Q6C5549030A3Q004661726D436F6E66696703083Q004175746F4661726D0100030C3Q004D696E696E67436F6E666967030A3Q004175746F4D696E696E6703073Q00436C65616E757003053Q007061697273030D3Q00556E6C6F6164436C65616E7570030B3Q00436F2Q6E656374696F6E73030A3Q00446973636F2Q6E6563740003203Q005B54686520466F7267655D20556E6C6F6164656420636F6D706C6574656C7921008A3Q00120C3Q00013Q00122Q000100028Q0002000100124Q00033Q00206Q000400206Q000500064Q000D00013Q0004413Q000D00010012043Q00063Q001204000100033Q0020870001000100040020870001000100052Q00813Q000200010012043Q00033Q0020875Q00040020875Q00070006733Q001700013Q0004413Q001700010012043Q00063Q001204000100033Q0020870001000100040020870001000100072Q00813Q000200010012043Q00033Q0020875Q00040020875Q00080006733Q002100013Q0004413Q002100010012043Q00063Q001204000100033Q0020870001000100040020870001000100082Q00813Q000200010012043Q00033Q0020875Q00040020875Q00090006733Q002B00013Q0004413Q002B00010012043Q00063Q001204000100033Q0020870001000100040020870001000100092Q00813Q000200010012043Q00033Q0020875Q00040020875Q000A0006733Q003500013Q0004413Q003500010012043Q00063Q001204000100033Q00208700010001000400208700010001000A2Q00813Q000200010012043Q00033Q0020875Q00040020875Q000B0006733Q003E00013Q0004413Q003E00010012043Q00033Q0020875Q00040020875Q000B002Q303Q000C000D0012043Q00033Q0020875Q00040020875Q000E0006733Q004700013Q0004413Q004700010012043Q00033Q0020875Q00040020875Q000E002Q303Q000F000D0012043Q00033Q0020875Q00040020875Q00100006733Q005700013Q0004413Q005700010012043Q00113Q001256000100033Q00202Q00010001000400202Q0001000100106Q0002000200044Q00550001001204000500064Q006C000600044Q00810005000200010006763Q0052000100020004413Q005200012Q002A8Q005F3Q0001000100124Q00033Q00206Q000400206Q001200064Q006900013Q0004413Q006900010012043Q00113Q001256000100033Q00202Q00010001000400202Q0001000100126Q0002000200044Q00670001001204000500064Q006C000600044Q00810005000200010006763Q0064000100020004413Q006400010012043Q00033Q0020875Q00040020875Q00130006733Q008000013Q0004413Q008000010012043Q00113Q001256000100033Q00202Q00010001000400202Q0001000100136Q0002000200044Q007E00010006730004007D00013Q0004413Q007D00010020870005000400140006730005007D00013Q0004413Q007D0001001204000500063Q00062B00063Q000100012Q006C3Q00044Q00810005000200012Q004800035Q0006763Q0074000100020004413Q007400010012043Q00033Q002Q303Q000400150012043Q00063Q00062B00010001000100012Q002A3Q00014Q002F3Q0002000100124Q00013Q00122Q000100168Q000200016Q00013Q00023Q00013Q00030A3Q00446973636F2Q6E65637400044Q002A7Q0020425Q00012Q00813Q000200012Q00203Q00017Q00013Q0003073Q0044657374726F7900044Q002A7Q0020425Q00012Q00813Q000200012Q00203Q00017Q00403Q0003053Q007072696E7403243Q005B54686520466F7267655D20466F72636520436C65616E757020737461727465643Q2E03023Q005F4703053Q00466F72676503093Q0052657365744661726D03053Q007063612Q6C030B3Q0052657365744D696E696E67030D3Q00526573657454656C65706F7274030B3Q00436F2Q6E656374696F6E7303053Q007061697273030A3Q00446973636F2Q6E65637403183Q005B436C65616E75705D20446973636F2Q6E65637465643A2003083Q00746F737472696E6703043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q00436861726163746572030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030D3Q00506C6174666F726D5374616E640100030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503093Q0047652Q74696E67557003073Q0052696754797065030F3Q0048756D616E6F6964526967547970652Q033Q0052313503093Q00486970486569676874027Q0040028Q0003043Q004865616403053Q00546F72736F030A3Q00552Q706572546F72736F030A3Q004C6F776572546F72736F2Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964652Q0103443Q005B436C65616E75705D20526573746F7265642043616E436F2Q6C69646520666F7220486561642F546F72736F206F6E6C79202864656661756C74206265686176696F722903103Q0048756D616E6F6964522Q6F745061727403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030E3Q0047657444657363656E64616E747303083Q00426F64794779726F030C3Q00426F647956656C6F63697479030C3Q00426F6479506F736974696F6E03093Q00426F6479466F726365030D3Q00416C69676E506F736974696F6E03103Q00416C69676E4F7269656E746174696F6E03073Q0044657374726F7903153Q005B436C65616E75705D2044657374726F7965643A2003093Q00436C612Q734E616D6503073Q00436C65616E757003063Q004E6F7469667903053Q005469746C6503103Q00436C65616E757020436F6D706C65746503073Q00436F6E74656E74031B3Q005068797369637320726573746F72656420746F206E6F726D616C2103083Q004475726174696F6E03233Q005B54686520466F7267655D20466F72636520436C65616E757020636F6D706C6574652100DE3Q002Q123Q00013Q00122Q000100028Q0002000100124Q00033Q00206Q000400064Q002500013Q0004413Q002500010012043Q00033Q0020875Q00040020875Q00050006733Q001100013Q0004413Q001100010012043Q00063Q001204000100033Q0020870001000100040020870001000100052Q00813Q000200010012043Q00033Q0020875Q00040020875Q00070006733Q001B00013Q0004413Q001B00010012043Q00063Q001204000100033Q0020870001000100040020870001000100072Q00813Q000200010012043Q00033Q0020875Q00040020875Q00080006733Q002500013Q0004413Q002500010012043Q00063Q001204000100033Q0020870001000100040020870001000100082Q00813Q000200010012043Q00033Q0020875Q00040006733Q004B00013Q0004413Q004B00010012043Q00033Q0020875Q00040020875Q00090006733Q004B00013Q0004413Q004B00010012043Q000A3Q001256000100033Q00202Q00010001000400202Q0001000100096Q0002000200044Q004500010006730004004400013Q0004413Q0044000100208700050004000B0006730005004400013Q0004413Q00440001001204000500063Q00062B00063Q000100012Q006C3Q00044Q004900050002000100122Q000500013Q00122Q0006000C3Q00122Q0007000D6Q000800036Q0007000200024Q0006000600074Q0005000200012Q004800035Q0006763Q0034000100020004413Q003400010012043Q00033Q0020875Q00042Q005400015Q0010093Q000900010012043Q000E3Q0020225Q000F00122Q000200108Q0002000200202Q00013Q001100202Q00020001001200062Q000200BD00013Q0004413Q00BD0001002042000300020013001219000500144Q000D0003000500020006730003006700013Q0004413Q00670001002Q3000030015001600201F00040003001700122Q000600183Q00202Q00060006001900202Q00060006001A4Q00040006000100202Q00040003001B00122Q000500183Q00202Q00050005001C00202Q00050005001D00062Q00040066000100050004413Q00660001002Q300003001E001F0004413Q00670001002Q300003001E00202Q0054000400043Q001233000500213Q00122Q000600223Q00122Q000700233Q00122Q000800246Q0004000400010012040005000A4Q006C000600044Q00400005000200070004413Q007C0001002042000A000200132Q006C000C00094Q000D000A000C0002000673000A007C00013Q0004413Q007C0001002042000B000A0025001219000D00264Q000D000B000D0002000673000B007C00013Q0004413Q007C0001002Q30000A0027002800067600050071000100020004413Q00710001001204000500013Q00124F000600296Q00050002000100202Q00050002001300122Q0007002A6Q00050007000200062Q00050089000100010004413Q00890001002042000500020013001219000700224Q000D0005000700020006730005009100013Q0004413Q009100010012040006002C3Q00201300060006002D00102Q0005002B000600122Q0006002C3Q00202Q00060006002D00102Q0005002E00060012040006000A3Q00204200070002002F2Q0007000700084Q006700063Q00080004413Q00BB0001002042000B000A0025001219000D00304Q000D000B000D0002000686000B00B4000100010004413Q00B40001002042000B000A0025001219000D00314Q000D000B000D0002000686000B00B4000100010004413Q00B40001002042000B000A0025001219000D00324Q000D000B000D0002000686000B00B4000100010004413Q00B40001002042000B000A0025001219000D00334Q000D000B000D0002000686000B00B4000100010004413Q00B40001002042000B000A0025001219000D00344Q000D000B000D0002000686000B00B4000100010004413Q00B40001002042000B000A0025001219000D00354Q000D000B000D0002000673000B00BB00013Q0004413Q00BB0001002042000B000A00362Q0084000B0002000100122Q000B00013Q00122Q000C00373Q00202Q000D000A00384Q000C000C000D4Q000B0002000100067600060096000100020004413Q009600012Q002A00036Q0047000300010001001204000300033Q002087000300030004000673000300D300013Q0004413Q00D30001001204000300033Q002087000300030004002087000300030039000673000300D300013Q0004413Q00D300010012040003000A3Q001256000400033Q00202Q00040004000400202Q0004000400394Q00030002000500044Q00D10001001204000800064Q006C000900074Q0081000800020001000676000300CE000100020004413Q00CE00012Q002A000300013Q00205300030003003A4Q00053Q000300302Q0005003B003C00302Q0005003D003E00302Q0005003F001F4Q00030005000100122Q000300013Q00122Q000400406Q0003000200016Q00013Q00013Q00013Q00030A3Q00446973636F2Q6E65637400044Q002A7Q0020425Q00012Q00813Q000200012Q00203Q00017Q00043Q0003023Q005F4703053Q00466F72676503093Q0053686F774C6F67554903093Q00486964654C6F675549011A3Q001204000100013Q0020870001000100020006730001001900013Q0004413Q001900010006733Q001000013Q0004413Q00100001001204000100013Q0020870001000100020020870001000100030006730001001900013Q0004413Q00190001001204000100013Q0020870001000100020020870001000100032Q00470001000100010004413Q00190001001204000100013Q0020870001000100020020870001000100040006730001001900013Q0004413Q00190001001204000100013Q0020870001000100020020870001000100042Q00470001000100012Q00203Q00017Q001D3Q0003023Q005F4703053Q00466F72676503073Q00436C65616E7570030D3Q00556E6C6F6164436C65616E7570030B3Q00436F2Q6E656374696F6E7303093Q0052657365744661726D030B3Q0052657365744D696E696E67030D3Q00526573657454656C65706F727403083Q00526573657446505303093Q00526573657453652Q6C030E3Q0052657365744175746F466F72676503083Q005265736574466C79030D3Q0052657365744D696E696E675549030D3Q005265736574506C617965725549030F3Q0052657365744175746F53652Q6C5549030D3Q0043616D6572615368616B65554903043Q007479706503053Q00526573657403083Q0066756E6374696F6E03053Q007063612Q6C030B3Q0043616D6572615368616B6503053Q00706169727303063Q004E6F7469667903053Q005469746C65030E3Q00526573657420436F6D706C65746503073Q00436F6E74656E74031C3Q00412Q6C207265736574202620636F6E666967732064656C657465642103083Q004475726174696F6E026Q00084000943Q0012043Q00013Q0020875Q00020006863Q0007000100010004413Q000700010012043Q00014Q005400015Q0010093Q000200010012043Q00013Q0020875Q00020020875Q00030006863Q0010000100010004413Q001000010012043Q00013Q0020875Q00022Q005400015Q0010093Q000300010012043Q00013Q0020875Q00020020875Q00040006863Q0019000100010004413Q001900010012043Q00013Q0020875Q00022Q005400015Q0010093Q000400010012043Q00013Q0020875Q00020020875Q00050006863Q0022000100010004413Q002200010012043Q00013Q0020875Q00022Q005400015Q0010093Q0005000100023F8Q003800015Q00122Q000200013Q00202Q00020002000200202Q0002000200064Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q0002000200074Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q0002000200084Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q0002000200094Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000A4Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000B4Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000C4Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000D4Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000E4Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000F4Q00010002000100122Q000100013Q00202Q00010001000200202Q00010001001000062Q0001006900013Q0004413Q00690001001204000100113Q00127C000200013Q00202Q00020002000200202Q00020002001000202Q0002000200124Q00010002000200262Q00010069000100130004413Q00690001001204000100143Q00123A000200013Q00202Q00020002000200202Q00020002001000202Q0002000200124Q00010002000100044Q007C0001001204000100013Q0020870001000100020020870001000100150006730001007C00013Q0004413Q007C0001001204000100113Q00127C000200013Q00202Q00020002000200202Q00020002001500202Q0002000200124Q00010002000200262Q0001007C000100130004413Q007C0001001204000100143Q001221000200013Q00202Q00020002000200202Q00020002001500202Q0002000200124Q000100020001001204000100163Q001256000200013Q00202Q00020002000200202Q0002000200034Q00010002000300044Q00850001001204000600144Q006C000700054Q008100060002000100067600010082000100020004413Q008200012Q002A00016Q0047000100010001001204000100143Q00023F000200014Q00250001000200014Q000100013Q00202Q0001000100174Q00033Q000300302Q00030018001900302Q0003001A001B00302Q0003001C001D4Q0001000300016Q00013Q00023Q00033Q0003043Q007479706503083Q0066756E6374696F6E03053Q007063612Q6C01093Q001204000100014Q006C00026Q005800010002000200261000010008000100020004413Q00080001001204000100034Q006C00026Q00810001000200012Q00203Q00017Q00053Q0003083Q006973666F6C64657203083Q00546865466F72676503053Q00706169727303093Q006C69737466696C657303053Q007063612Q6C00163Q0012043Q00013Q001219000100024Q00583Q000200020006733Q001500013Q0004413Q001500010012043Q00033Q001268000100043Q00122Q000200026Q000100029Q00000200044Q00100001001204000500053Q00062B00063Q000100012Q006C3Q00044Q00810005000200012Q004800035Q0006763Q000B000100020004413Q000B00010012043Q00053Q00023F000100014Q00813Q000200012Q00203Q00013Q00023Q00013Q0003073Q0064656C66696C6500043Q0012043Q00014Q002A00016Q00813Q000200012Q00203Q00017Q00023Q0003093Q0064656C666F6C64657203083Q00546865466F72676500043Q0012043Q00013Q001219000100024Q00813Q000200012Q00203Q00017Q00043Q0003013Q0052025Q00E06F4003013Q004703013Q0042010C4Q007200013Q000300202Q00023Q000100202Q00020002000200102Q00010001000200202Q00023Q000300202Q00020002000200102Q00010003000200202Q00023Q000400202Q00020002000200102Q0001000400024Q000100028Q00017Q00053Q0003063Q00436F6C6F723303073Q0066726F6D52474203013Q005203013Q004703013Q004201083Q00121A000100013Q00202Q00010001000200202Q00023Q000300202Q00033Q000400202Q00043Q00054Q000100046Q00019Q0000017Q00023Q0003013Q002F03053Q002E72666C64010C4Q002A00015Q0006570002000400013Q0004413Q000400012Q002A000200014Q00580001000200022Q0028000200023Q00122Q000300016Q000400013Q00122Q000500026Q0002000200054Q000200028Q00017Q000D3Q0003053Q00706169727303053Q00466C61677303043Q007479706503053Q007461626C6503043Q0054797065030B3Q00436F6C6F725069636B657203053Q00436F6C6F7203063Q00747970656F66030C3Q0043752Q72656E7456616C756503073Q00622Q6F6C65616E0100030E3Q0043752Q72656E744B657962696E64030D3Q0043752Q72656E744F7074696F6E003E4Q003E7Q00122Q000100016Q00025Q00202Q00020002000200062Q00020007000100010004413Q000700012Q005400026Q00400001000200030004413Q003A0001001204000600034Q006C000700054Q00580006000200020026100006003A000100040004413Q003A000100208700060005000500261000060019000100060004413Q001900010020870006000500070006730006001900013Q0004413Q001900012Q002A000600013Q0020870007000500072Q00580006000200022Q00783Q000400060004413Q003A00012Q005D000600063Q001204000700083Q0020870008000500092Q00580007000200020026100007002F0001000A0004413Q002F0001002087000700050009002610000700240001000B0004413Q002400012Q004500065Q0004413Q003900010020870007000500090006570006002E000100070004413Q002E000100208700070005000C0006570006002E000100070004413Q002E000100208700070005000D0006570006002E000100070004413Q002E00010020870006000500070004413Q0039000100208700070005000900065700060039000100070004413Q0039000100208700070005000C00065700060039000100070004413Q0039000100208700070005000D00065700060039000100070004413Q003900010020870006000500072Q00783Q0004000600067600010009000100020004413Q000900012Q000A3Q00024Q00203Q00017Q00053Q0003093Q00777269746566696C6503183Q0046696C6573797374656D206E6F742073752Q706F7274656403083Q006973666F6C646572030A3Q006D616B65666F6C646572030A3Q004A534F4E456E636F6465001E3Q0012043Q00013Q0006863Q0006000100010004413Q000600012Q00457Q001219000100024Q006A3Q00033Q0012043Q00033Q0006733Q001100013Q0004413Q001100010012043Q00034Q002A00016Q00583Q000200020006863Q0011000100010004413Q001100010012043Q00044Q002A00016Q00813Q000200012Q002A3Q00014Q00753Q0001000200122Q000100016Q000200026Q0002000100024Q000300033Q00202Q0003000300054Q00058Q000300056Q00013Q00014Q000100016Q000100028Q00017Q000B3Q0003063Q00697366696C6503173Q00436F6E6669672066696C65206E6F7420666F756E643A2003053Q007063612Q6C031C3Q004661696C656420746F206465636F646520636F6E666967206461746103053Q00706169727303053Q00466C6167730003043Q007479706503053Q007461626C652Q033Q0053657403083Q0066756E6374696F6E01393Q001204000100013Q0006730001000800013Q0004413Q00080001001204000100014Q006C00026Q00580001000200020006860001000D000100010004413Q000D00012Q004500015Q001219000200024Q006C00036Q00880002000200032Q006A000100033Q001204000100033Q00062B00023Q000100022Q002A8Q006C8Q004000010002000200068600010017000100010004413Q001700012Q004500035Q001219000400044Q006A000300033Q001204000300054Q002A000400013Q0020870004000400060006860004001D000100010004413Q001D00012Q005400046Q00400003000200050004413Q003400012Q007D00080002000600263700080032000100070004413Q00320001001204000900084Q006C000A00074Q005800090002000200261000090032000100090004413Q00320001001204000900083Q002087000A0007000A2Q0058000900020002002610000900320001000B0004413Q00320001001204000900033Q00062B000A0001000100032Q006C3Q00074Q006C3Q00084Q002A3Q00024Q00810009000200012Q004800086Q004800065Q0006760003001F000100020004413Q001F00012Q0045000300014Q000A000300024Q00203Q00013Q00023Q00023Q00030A3Q004A534F4E4465636F646503083Q007265616466696C6500084Q003D7Q00206Q000100122Q000200026Q000300016Q000200039Q009Q008Q00017Q00053Q0003043Q0054797065030B3Q00436F6C6F725069636B657203043Q007479706503053Q007461626C652Q033Q0053657400154Q002A7Q0020875Q00010026103Q0010000100020004413Q001000010012043Q00034Q002A000100014Q00583Q000200020026103Q0010000100040004413Q001000012Q002A7Q00202D5Q00054Q000200026Q000300016Q000200039Q00000100044Q001400012Q002A7Q0020425Q00052Q002A000200014Q00743Q000200012Q00203Q00017Q000C3Q00030F3Q00436F6E6669674E616D65496E7075742Q033Q0053657403063Q004E6F7469667903053Q005469746C65030B3Q00436F6E666967204E616D6503073Q00436F6E74656E74030A3Q005361766564206173202703243Q00272E2052656C6F61642073637269707420746F20612Q706C79206175746F2D736176652E03083Q004475726174696F6E026Q00084003083Q00746F737472696E67026Q001040012E4Q002A00015Q0006730001000600013Q0004413Q000600012Q004500016Q008500016Q00203Q00014Q002A000100014Q005100028Q0001000200024Q000100026Q000200036Q000300016Q00020002000300062Q0002002300013Q0004413Q002300010006770001001700013Q0004413Q001700012Q0045000400014Q004300045Q00122Q000400013Q00202Q0004000400024Q000600016Q0004000600012Q002A000400043Q00204C0004000400034Q00063Q000300302Q00060004000500122Q000700076Q000800013Q00122Q000900086Q00070007000900102Q00060006000700302Q00060009000A4Q00040006000100044Q002D00012Q002A000400043Q0020010004000400034Q00063Q000300302Q00060004000500122Q0007000B6Q000800036Q00070002000200102Q00060006000700302Q00060009000C4Q0004000600012Q00203Q00017Q000B3Q0003053Q007063612Q6C03063Q004E6F7469667903053Q005469746C6503053Q005361766564030B3Q0053617665204661696C656403073Q00436F6E74656E7403173Q00436F6E66696775726174696F6E20736176656420746F2003083Q00746F737472696E6703083Q004475726174696F6E027Q0040026Q00104000233Q0012043Q00013Q00062B00013Q000100012Q002A8Q00063Q000200014Q000200013Q00202Q0002000200024Q00043Q000300064Q000C00013Q0004413Q000C0001001219000500043Q0006860005000D000100010004413Q000D0001001219000500053Q0010090004000300050006733Q001600013Q0004413Q00160001001219000500074Q002A000600024Q006F0006000100022Q008800050005000600068600050019000100010004413Q00190001001204000500084Q006C000600014Q00580005000200020010090004000600050006733Q001F00013Q0004413Q001F00010012190005000A3Q00068600050020000100010004413Q002000010012190005000B3Q0010090004000900052Q00740002000400012Q00203Q00013Q00013Q00013Q0003053Q00652Q726F7200084Q002A8Q00323Q000100010006863Q0007000100010004413Q00070001001204000200014Q006C000300014Q00810002000200012Q00203Q00017Q000B3Q0003053Q007063612Q6C03063Q004E6F7469667903053Q005469746C6503063Q004C6F61646564030B3Q004C6F6164204661696C656403073Q00436F6E74656E74031A3Q00436F6E66696775726174696F6E206C6F616465642066726F6D2003083Q00746F737472696E6703083Q004475726174696F6E027Q0040026Q00104000243Q0012043Q00013Q00062B00013Q000100022Q002A8Q002A3Q00014Q00063Q000200014Q000200023Q00202Q0002000200024Q00043Q000300064Q000D00013Q0004413Q000D0001001219000500043Q0006860005000E000100010004413Q000E0001001219000500053Q0010090004000300050006733Q001700013Q0004413Q00170001001219000500074Q002A00066Q006F0006000100022Q00880005000500060006860005001A000100010004413Q001A0001001204000500084Q006C000600014Q00580005000200020010090004000600050006733Q002000013Q0004413Q002000010012190005000A3Q00068600050021000100010004413Q002100010012190005000B3Q0010090004000900052Q00740002000400012Q00203Q00013Q00013Q00013Q0003053Q00652Q726F72000B4Q00359Q003Q000100024Q000100016Q00028Q00010002000200062Q0001000A000100010004413Q000A0001001204000300014Q006C000400024Q00810003000200012Q00203Q00017Q00133Q00027Q0040028Q0003063Q00697366696C6503083Q007265616466696C6503043Q002E6C756103053Q007063612Q6C03053Q007072696E7403213Q005B54686520466F7267655D204C6F61646564206C6F63616C206D6F64756C653A2003043Q007761726E03213Q005B54686520466F7267655D204661696C656420746F206C6F6164206C6F63616C2003023Q003A2003083Q00746F737472696E67026Q00F03F03143Q005B54686520466F7267655D204C6F616465643A20031B3Q005B54686520466F7267655D204661696C656420746F206C6F61642003093Q0020612Q74656D70742003043Q007461736B03043Q0077616974026Q00E03F014E3Q001219000100013Q001219000200023Q001204000300033Q0006730003002600013Q0004413Q00260001001204000300043Q0006730003002600013Q0004413Q00260001001204000300034Q006E00045Q00122Q000500056Q0004000400054Q00030002000200062Q0003002600013Q0004413Q00260001001204000300063Q00062B00043Q000100012Q006C8Q00400003000200040006730003001D00013Q0004413Q001D0001001204000500073Q001231000600086Q00078Q0006000600074Q0005000200014Q000500016Q000500023Q00044Q00260001001204000500093Q0012550006000A6Q00075Q00122Q0008000B3Q00122Q0009000C6Q000A00046Q0009000200024Q0006000600094Q0005000200010006020002004B000100010004413Q004B000100201800020002000D001204000300063Q00062B00040001000100032Q002A8Q006C8Q006C3Q00024Q00400003000200040006730003003900013Q0004413Q00390001001204000500073Q0012310006000E6Q00078Q0006000600074Q0005000200014Q000500016Q000500023Q00044Q00260001001204000500093Q0012240006000F6Q00075Q00122Q000800106Q000900023Q00122Q000A000B3Q00122Q000B000C6Q000C00046Q000B000200024Q00060006000B4Q00050002000100062Q00020026000100010004413Q00260001001204000500113Q00208700050005001200106B0006001300022Q00810005000200010004413Q002600012Q004500036Q000A000300024Q00203Q00013Q00023Q00073Q0003083Q007265616466696C6503043Q002E6C7561030A3Q006C6F6164737472696E6703053Q00652Q726F7203163Q0053796E74617820452Q726F7220696E206C6F63616C2003023Q003A2003083Q00746F737472696E6700173Q0012263Q00016Q00015Q00122Q000200026Q0001000100026Q0002000200122Q000100036Q00028Q00010002000200062Q00010013000100010004413Q00130001001204000300043Q00127F000400056Q00055Q00122Q000600063Q00122Q000700076Q000800026Q0007000200024Q0004000400074Q0003000200012Q006C000300014Q0008000300014Q005A00036Q00203Q00017Q000D3Q0003073Q002E6C75613F763D03083Q00746F737472696E6703043Q007469636B03053Q007072696E7403163Q005B54686520466F7267655D204665746368696E673A20030A3Q002028612Q74656D70742003013Q002903043Q0067616D6503073Q00482Q7470476574030A3Q006C6F6164737472696E6703053Q00652Q726F7203103Q0053796E74617820452Q726F7220696E2003023Q003A2000274Q00829Q00000100013Q00122Q000200013Q00122Q000300023Q00122Q000400036Q000400016Q00033Q00028Q000300122Q000100043Q00122Q000200056Q00035Q00122Q000400066Q000500023Q00122Q000600076Q0002000200064Q00010002000100122Q000100083Q00202Q0001000100094Q00038Q000400016Q00010004000200122Q0002000A6Q000300016Q00020002000300062Q00020023000100010004413Q002300010012040004000B3Q00127F0005000C6Q000600013Q00122Q0007000D3Q00122Q000800026Q000900036Q0008000200024Q0005000500084Q0004000200012Q006C000400024Q0008000400014Q005A00046Q00203Q00017Q001F3Q0003043Q007461736B03043Q0077616974026Q00E03F028Q0003063Q00697061697273026Q33D33F026Q00F03F03053Q007461626C6503063Q00696E7365727403053Q007072696E7403133Q005B54686520466F7267655D204C6F616465642003013Q002F03083Q00206D6F64756C657303053Q007063612Q6C033A3Q005B54686520466F7267655D20536B692Q70696E67204C6F6164436F6E66696775726174696F6E20286E6F206D6F64756C6573206C6F616465642903063Q004E6F7469667903053Q005469746C6503093Q0054686520466F72676503073Q00436F6E74656E7403073Q004C6F6164656420030A3Q0020286661696C65643A2003063Q00636F6E63617403023Q002C2003013Q0029034Q0003013Q002103083Q004475726174696F6E026Q00084003073Q005761726E696E6703243Q004E6F206D6F64756C6573206C6F616465642E20436865636B207365727665722055524C2E026Q00144000583Q0012593Q00013Q00206Q000200122Q000100038Q0002000100124Q00046Q00015Q00122Q000200056Q00038Q00020002000400044Q001A0001001204000700013Q00206200070007000200122Q000800066Q0007000200014Q000700016Q000800066Q00070002000200062Q0007001500013Q0004413Q001500010020185Q00070004413Q001A0001001204000700083Q0020870007000700092Q006C000800014Q006C000900064Q00740007000900010006760002000A000100020004413Q000A00010012040002000A3Q00127A0003000B6Q00045Q00122Q0005000C6Q00068Q000600063Q00122Q0007000D6Q0003000300074Q00020002000100122Q000200013Q00202Q00020002000200122Q000300036Q000200020001000E2Q0004003000013Q0004413Q003000010012040002000E3Q00062B00033Q000100012Q002A3Q00024Q00810002000200010004413Q003300010012040002000A3Q0012190003000F4Q0081000200020001000E500004005000013Q0004413Q005000012Q002A000200023Q0020690002000200104Q00043Q000300302Q00040011001200122Q000500146Q00065Q00122Q0007000D6Q000800013Q000E2Q00040049000100080004413Q00490001001219000800153Q00121E000900083Q00202Q0009000900164Q000A00013Q00122Q000B00176Q0009000B000200122Q000A00186Q00080008000A00062Q0008004A000100010004413Q004A0001001219000800193Q0012190009001A6Q00050005000900102Q00040013000500302Q0004001B001C4Q00020004000100044Q005700012Q002A000200023Q0020140002000200104Q00043Q000300302Q00040011001D00302Q00040013001E00302Q0004001B001F4Q0002000400012Q00203Q00013Q00013Q00013Q0003113Q004C6F6164436F6E66696775726174696F6E00044Q002A7Q0020425Q00012Q00813Q000200012Q00203Q00017Q00", GetFEnv(), ...);
