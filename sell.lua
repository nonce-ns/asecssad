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
				if (Enum <= 87) then
					if (Enum <= 43) then
						if (Enum <= 21) then
							if (Enum <= 10) then
								if (Enum <= 4) then
									if (Enum <= 1) then
										if (Enum > 0) then
											do
												return;
											end
										else
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
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
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
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										end
									elseif (Enum <= 2) then
										local A;
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
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
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 3) then
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										do
											return Stk[A], Stk[A + 1];
										end
									end
								elseif (Enum <= 7) then
									if (Enum <= 5) then
										local A;
										local K;
										local B;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
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
									elseif (Enum > 6) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
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
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum <= 8) then
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
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 9) then
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
								else
									local A;
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 15) then
								if (Enum <= 12) then
									if (Enum == 11) then
										local A;
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
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
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
								elseif (Enum <= 13) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum == 14) then
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
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
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
									local A;
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
									Stk[Inst[2]] = Env[Inst[3]];
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
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 18) then
								if (Enum <= 16) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
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
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 17) then
									local A;
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
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
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
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 19) then
								local A;
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
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Enum == 20) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 32) then
							if (Enum <= 26) then
								if (Enum <= 23) then
									if (Enum > 22) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
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
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum <= 24) then
									Stk[Inst[2]]();
								elseif (Enum > 25) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
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
							elseif (Enum <= 29) then
								if (Enum <= 27) then
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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 28) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
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
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 30) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 31) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
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
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 37) then
							if (Enum <= 34) then
								if (Enum == 33) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
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
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
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
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 35) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 36) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
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
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local Edx;
								local Limit;
								local Results;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A]()};
								Limit = Inst[4];
								Edx = 0;
								for Idx = A, Limit do
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
						elseif (Enum <= 40) then
							if (Enum <= 38) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
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
							elseif (Enum > 39) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
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
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] ~= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
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
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 41) then
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
						elseif (Enum == 42) then
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
							Stk[Inst[2]] = Inst[3] ~= 0;
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
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
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
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 65) then
						if (Enum <= 54) then
							if (Enum <= 48) then
								if (Enum <= 45) then
									if (Enum > 44) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] <= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									end
								elseif (Enum <= 46) then
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
								elseif (Enum > 47) then
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local B;
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
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
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
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 51) then
								if (Enum <= 49) then
									local A;
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
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 50) then
									local B;
									local A;
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
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 52) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
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
							elseif (Enum == 53) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 59) then
							if (Enum <= 56) then
								if (Enum == 55) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
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
								else
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								end
							elseif (Enum <= 57) then
								VIP = Inst[3];
							elseif (Enum > 58) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
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
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 62) then
							if (Enum <= 60) then
								local A;
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum > 61) then
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 63) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum == 64) then
							local Edx;
							local Results;
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
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
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
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 76) then
						if (Enum <= 70) then
							if (Enum <= 67) then
								if (Enum > 66) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
									do
										return;
									end
								end
							elseif (Enum <= 68) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							elseif (Enum == 69) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
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
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 73) then
							if (Enum <= 71) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							elseif (Enum == 72) then
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
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 74) then
							local A;
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
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 75) then
							local B;
							local A;
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
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
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
						end
					elseif (Enum <= 81) then
						if (Enum <= 78) then
							if (Enum == 77) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 79) then
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
							Stk[Inst[2]] = {};
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
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						elseif (Enum > 80) then
							do
								return Stk[Inst[2]];
							end
						else
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
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 84) then
						if (Enum <= 82) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							do
								return;
							end
						elseif (Enum > 83) then
							local A;
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A;
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
					elseif (Enum <= 85) then
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					elseif (Enum == 86) then
						local K;
						local B;
						local A;
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
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
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
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
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
				elseif (Enum <= 131) then
					if (Enum <= 109) then
						if (Enum <= 98) then
							if (Enum <= 92) then
								if (Enum <= 89) then
									if (Enum == 88) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
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
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum <= 90) then
									local A;
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
									Stk[Inst[2]] = Env[Inst[3]];
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
									Stk[Inst[2]] = Env[Inst[3]];
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
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 91) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
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
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
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
							elseif (Enum <= 95) then
								if (Enum <= 93) then
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
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum == 94) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
								elseif (Stk[Inst[2]] ~= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 96) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
								do
									return;
								end
							elseif (Enum == 97) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 103) then
							if (Enum <= 100) then
								if (Enum > 99) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
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
							elseif (Enum <= 101) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							elseif (Enum == 102) then
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
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						elseif (Enum <= 106) then
							if (Enum <= 104) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 105) then
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 107) then
							local A;
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
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum == 108) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 120) then
						if (Enum <= 114) then
							if (Enum <= 111) then
								if (Enum == 110) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A;
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
							elseif (Enum <= 112) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum == 113) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
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
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum <= 117) then
							if (Enum <= 115) then
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
							elseif (Enum > 116) then
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
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
							end
						elseif (Enum <= 118) then
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
						elseif (Enum > 119) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A]();
						end
					elseif (Enum <= 125) then
						if (Enum <= 122) then
							if (Enum > 121) then
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
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 123) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
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
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 124) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							do
								return;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						end
					elseif (Enum <= 128) then
						if (Enum <= 126) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum == 127) then
							local A;
							Stk[Inst[2]]();
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
						else
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
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
						end
					elseif (Enum <= 129) then
						local B;
						local A;
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Stk[Inst[4]];
						if B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					elseif (Enum > 130) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					else
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
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 153) then
					if (Enum <= 142) then
						if (Enum <= 136) then
							if (Enum <= 133) then
								if (Enum == 132) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 134) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							elseif (Enum == 135) then
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 139) then
							if (Enum <= 137) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							elseif (Enum == 138) then
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
								do
									return;
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 140) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						elseif (Enum > 141) then
							local Results;
							local Edx;
							local Results, Limit;
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
							local K;
							local B;
							local A;
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
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 147) then
						if (Enum <= 144) then
							if (Enum > 143) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
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
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 145) then
							local A;
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum > 146) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 150) then
						if (Enum <= 148) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						elseif (Enum == 149) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 151) then
						local A;
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
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
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					elseif (Enum == 152) then
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
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
							if (Mvm[1] == 121) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum <= 164) then
					if (Enum <= 158) then
						if (Enum <= 155) then
							if (Enum == 154) then
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
								do
									return;
								end
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 156) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum == 157) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
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
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 161) then
						if (Enum <= 159) then
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 160) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						else
							local B;
							local A;
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 162) then
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
					elseif (Enum == 163) then
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
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
						local K;
						local B;
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
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 169) then
					if (Enum <= 166) then
						if (Enum == 165) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 167) then
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						do
							return;
						end
					elseif (Enum == 168) then
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
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Stk[Inst[4]];
						if B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 172) then
					if (Enum <= 170) then
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
					elseif (Enum > 171) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
				elseif (Enum <= 173) then
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
				elseif (Enum > 174) then
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
					Stk[Inst[2]][Inst[3]] = Inst[4];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Inst[4];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = {};
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]];
				else
					local A;
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A](Stk[A + 1]);
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
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
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
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A](Stk[A + 1]);
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!493Q0003023Q006F7303053Q00636C6F636B03043Q007461736B03043Q0077616974026Q00E03F03023Q005F4703053Q00466F72676503043Q005461627303063Q00506C6179657203083Q005261796669656C64026Q00244003043Q007761726E032C3Q005B53652Q6C5D20446570656E64656E63696573206E6F742072656164793B2061626F7274696E67206C6F616403043Q0067616D65030A3Q004765745365727669636503073Q00506C617965727303113Q005265706C69636174656453746F72616765030A3Q0052756E53657276696365030A3Q004775695365727669636503093Q00576F726B7370616365030B3Q004C6F63616C506C6179657203083Q004175746F53652Q6C0100030C3Q0053652Q6C496E74657276616C026Q003E40030C3Q0053652Q6C432Q6F6C646F776E027Q0040030D3Q00536B69704661766F72697465732Q0103143Q004E6F54656C65706F72744166746572466972737403053Q007061697273030A3Q0053652Q6C436F6E66696703113Q0053652Q6C44656661756C74436F6E666967028Q00030E3Q00436861726163746572412Q64656403073Q00436F2Q6E656374026Q003440026Q000CC0026Q002040030C3Q0054696E7920452Q73656E6365030D3Q00536D612Q6C20452Q73656E6365030E3Q004D656469756D20452Q73656E6365030D3Q004C6172676520452Q73656E6365030F3Q004772656174657220452Q73656E636503103Q005375706572696F7220452Q73656E6365030C3Q004570696320452Q73656E636503113Q004C6567656E6461727920452Q73656E6365030D3Q0053696D706C654C616E7465726E030A3Q00506F7274616C542Q6F6C03163Q004368726973746D61734576656E7443752Q72656E637903043Q004D697363030A3Q0045717569706D656E747303043Q00722Q6F74002Q033Q0063747803043Q0074696D6503093Q00526573657453652Q6C03083Q0053652Q6C4F6E636503123Q0053652Q6C4F6E63654E6F54656C65706F727403153Q0053652Q6C4F6E6365466F72636554656C65706F7274030D3Q0053746172744175746F53652Q6C030C3Q0053746F704175746F53652Q6C03113Q0047657453652Q6C506C617965724461746103053Q007461626C6503063Q00696E7365727403073Q00436C65616E757003133Q004D6F64756C652076312E30206C6F616465642103063Q004E6F7469667903053Q005469746C65030B3Q0053652Q6C204D6F64756C6503073Q00436F6E74656E74030C3Q0076312E30204C6F616465642103083Q004475726174696F6E002F012Q0012A53Q00013Q0020165Q00022Q00773Q000100020012A5000100033Q00207300010001000400122Q000200056Q00010002000100122Q000100063Q00202Q00010001000700062Q0001001B00013Q0004393Q001B00010012A5000100063Q0020160001000100070020160001000100080006140001001B00013Q0004393Q001B00010012A5000100063Q0020160001000100070020160001000100080020160001000100090006140001001B00013Q0004393Q001B00010012A5000100063Q00201600010001000700201600010001000A0006A900010021000100010004393Q002100010012A5000100013Q0020160001000100022Q00770001000100022Q007C000100013Q000E9B000B0003000100010004393Q000300010012A5000100063Q0020160001000100070006140001003500013Q0004393Q003500010012A5000100063Q0020160001000100070020160001000100080006140001003500013Q0004393Q003500010012A5000100063Q0020160001000100070020160001000100080020160001000100090006140001003500013Q0004393Q003500010012A5000100063Q00201600010001000700201600010001000A0006A900010039000100010004393Q003900010012A50001000C3Q0012320002000D4Q00840001000200012Q00013Q00013Q0012A50001000E3Q0020AA00010001000F00122Q000300106Q00010003000200122Q0002000E3Q00202Q00020002000F00122Q000400116Q00020004000200122Q0003000E3Q00202Q00030003000F00122Q000500124Q006D0003000500020012760004000E3Q00202Q00040004000F00122Q000600136Q00040006000200122Q0005000E3Q00202Q00050005000F00122Q000700146Q00050007000200202Q00060001001500122Q000700063Q0020160007000700070020AF00080007000A4Q00093Q000500302Q00090016001700302Q00090018001900302Q0009001A001B00302Q0009001C001D00302Q0009001E001D4Q000A5Q00122Q000B001F6Q000C00094Q0035000B0002000D0004393Q005D00012Q004D000A000E000F00060A000B005C000100020004393Q005C00010010AD00070020000A0010450007002100094Q000B000B3Q00122Q000C00226Q000D8Q000E5Q00062Q0006006C00013Q0004393Q006C0001002016000F000600230020AC000F000F002400069900113Q000100012Q00793Q000E4Q0083000F001100012Q00A1000F00124Q001C00135Q00122Q001400253Q00122Q001500263Q00122Q001600276Q00173Q000800302Q00170028001D00302Q00170029001D00302Q0017002A001D00302Q0017002B001D00302Q0017002C001D0030590017002D001D0030480017002E001D00302Q0017002F001D4Q00183Q000500302Q00180030001D00302Q00180031001D00302Q00180032001D00302Q00180033001D00302Q00180034001D000286001900013Q000699001A0002000100012Q00793Q00083Q000286001B00033Q000699001C0004000100012Q00793Q001B3Q000286001D00054Q005D001E3Q000300302Q001E0035003600302Q001E0037003600302Q001E003800224Q001F00203Q00122Q002100223Q00069900220006000100052Q00793Q001F4Q00793Q00024Q00793Q001E4Q00793Q00204Q00793Q00213Q00069900230007000100032Q00793Q00224Q00793Q00024Q00793Q001E3Q00069900240008000100032Q00793Q00204Q00793Q00214Q00793Q00193Q00069900250009000100012Q00793Q00063Q0006990026000A000100012Q00793Q00023Q0006990027000B000100012Q00793Q00053Q0006990028000C000100012Q00793Q00063Q0002860029000D3Q000699002A000E000100022Q00793Q00284Q00793Q00293Q000699002B000F000100012Q00793Q002A3Q000699002C0010000100012Q00793Q002A3Q000699002D0011000100022Q00793Q00024Q00793Q00063Q000699002E0012000100032Q00793Q002B4Q00793Q002C4Q00793Q002D3Q000699002F0013000100012Q00793Q00063Q00069900300014000100012Q00793Q00053Q000286003100153Q000286003200163Q00069900330017000100072Q00793Q002E4Q00793Q00194Q00793Q00314Q00793Q00184Q00793Q00174Q00793Q00324Q00793Q000A3Q00069900340018000100022Q00793Q00054Q00793Q00063Q000286003500193Q0006990036001A000100022Q00793Q000F4Q00793Q00053Q0006990037001B000100022Q00793Q000F4Q00793Q00153Q0006990038001C000100012Q00793Q000F3Q0006990039001D000100072Q00793Q00134Q00793Q00114Q00793Q00124Q00793Q00344Q00793Q00354Q00793Q00104Q00793Q00383Q000699003A001E0001000D2Q00793Q00134Q00793Q00394Q00793Q00344Q00793Q00354Q00793Q00194Q00793Q00364Q00793Q00374Q00793Q00124Q00793Q00034Q00793Q00114Q00793Q00164Q00793Q00144Q00793Q00103Q000699003B001F000100042Q00793Q00234Q00793Q00194Q00793Q00204Q00793Q00213Q000699003C0020000100042Q00793Q00344Q00793Q00194Q00793Q00044Q00793Q00063Q000699003D0021000100142Q00793Q000D4Q00793Q00254Q00793Q00334Q00793Q001A4Q00793Q00194Q00793Q00264Q00793Q00274Q00793Q00344Q00793Q00354Q00793Q000E4Q00793Q00244Q00793Q003B4Q00793Q000A4Q00793Q00304Q00793Q003C4Q00793Q000C4Q00793Q001D4Q00793Q002F4Q00793Q001C4Q00793Q00023Q000699003E0022000100062Q00793Q000B4Q00793Q000A4Q00793Q000D4Q00793Q000C4Q00793Q00194Q00793Q003D3Q000699003F0023000100012Q00793Q000A3Q00069900400024000100062Q00793Q000A4Q00793Q000D4Q00793Q000E4Q00793Q000C4Q00793Q00094Q00793Q00193Q0010AD0007003900400010AD0007003A003D00069900400025000100012Q00793Q003D3Q0010AD0007003B004000069900400026000100012Q00793Q003D3Q0010AD0007003C00400010AD0007003D003E0010AD0007003E003F0010AD0007003F002E00069900400027000100032Q00793Q003F4Q00793Q00394Q00793Q00193Q00122F004100403Q00202Q00410041004100202Q0042000700424Q004300406Q0041004300014Q004100193Q00122Q004200436Q00410002000100202Q0041000800444Q00433Q000300305900430045004600305900430047004800305900430049001B2Q00830041004300012Q00013Q00013Q00288Q00034Q00478Q008C8Q00013Q00017Q00053Q0003053Q007072696E7403073Q005B53652Q6C5D2003023Q005F4703053Q00466F7267652Q033Q004C6F6701163Q00124B000100013Q00122Q000200026Q00038Q0002000200034Q00010002000100122Q000100033Q00202Q00010001000400062Q0001001500013Q0004393Q001500010012A5000100033Q0020160001000100040020160001000100050006140001001500013Q0004393Q001500010012A5000100033Q00200500010001000400202Q00010001000500122Q000200026Q00038Q0002000200034Q0001000200012Q00013Q00017Q00013Q0003053Q007063612Q6C03083Q0012A5000300013Q00069900043Q000100042Q009C8Q00798Q00793Q00014Q00793Q00024Q00840003000200012Q00013Q00013Q00013Q00053Q0003063Q004E6F7469667903053Q005469746C6503073Q00436F6E74656E7403083Q004475726174696F6E027Q0040000E4Q00827Q00206Q00014Q00023Q00034Q000300013Q00102Q0002000200034Q000300023Q00102Q0002000300034Q000300033Q00062Q0003000B000100010004393Q000B0001001232000300053Q0010AD0002000400032Q00833Q000200012Q00013Q00017Q00073Q0003043Q007479706503053Q007461626C6503063Q0072617767657403063Q006E756D626572028Q0003073Q00622Q6F6C65616E0100021E3Q0012A5000200014Q007900036Q009300020002000200265F00020007000100020004393Q000700012Q004700026Q0051000200023Q0012A5000200034Q009000038Q000400016Q00020004000200122Q000300016Q000400026Q00030002000200262Q00030013000100040004393Q001300010020443Q000100052Q0047000300014Q0051000300023Q0012A5000300014Q0079000400024Q00930003000200020026040003001B000100060004393Q001B00010020443Q000100072Q0047000300014Q0051000300024Q004700036Q0051000300024Q00013Q00017Q00043Q0003043Q007479706503053Q007461626C65030C3Q0044617368432Q6F6C646F776E03073Q0044617368696E6701183Q0012A5000100014Q007900026Q009300010002000200265F00010007000100020004393Q000700012Q004700016Q0051000100024Q004700016Q009F00028Q00035Q00122Q000400036Q00020004000200062Q0002000F00013Q0004393Q000F00012Q0047000100014Q009C00026Q007900035Q001232000400044Q006D0002000400020006140002001600013Q0004393Q001600012Q0047000100014Q0051000100024Q00013Q00017Q00083Q0003043Q007479706503063Q00737472696E6703053Q006C6F776572030A3Q006E6F6D6F76656D656E74030F3Q0064697361626C656261636B7061636B03063Q006E6F64617368030B3Q0064697361626C6564617368030E3Q006E6F64617368632Q6F6C646F776E01173Q0012A5000100014Q007900026Q009300010002000200265F00010007000100020004393Q000700012Q004700016Q0051000100023Q0020AC00013Q00032Q009300010002000200265F00010014000100040004393Q0014000100265F00010014000100050004393Q0014000100265F00010014000100060004393Q0014000100265F00010014000100070004393Q0014000100265F00010014000100080004393Q001400012Q006A00026Q0047000200014Q0051000200024Q00013Q00017Q00053Q0003093Q00436F2Q6E6563746564030E3Q0046696E6446697273744368696C64030E3Q004469616C6F67756552656D6F7465030D3Q004F6E436C69656E744576656E7403073Q00436F2Q6E65637400194Q009C7Q0006143Q000800013Q0004393Q000800012Q009C7Q0020165Q00010006143Q000800013Q0004393Q000800012Q00013Q00014Q009C3Q00013Q00202A5Q000200122Q000200036Q000300018Q0003000200064Q0010000100010004393Q001000012Q00013Q00013Q00201600013Q00040020AC00010001000500069900033Q000100032Q009C3Q00024Q009C3Q00034Q009C3Q00044Q006D0001000300022Q008C00016Q00013Q00013Q00013Q00063Q0003043Q00722Q6F742Q033Q0063747803043Q0074696D6503023Q006F7303053Q00636C6F636B030F3Q0053652Q6C436F6E6669726D4D69736302114Q002000025Q00102Q000200016Q00025Q00102Q0002000200014Q00025Q00122Q000300043Q00202Q0003000300054Q00030001000200102Q00020003000300264Q0010000100060004393Q001000012Q008C000100013Q0012A5000200043Q0020160002000200052Q00770002000100022Q008C000200024Q00013Q00017Q000E3Q00030E3Q0046696E6446697273744368696C64030E3Q004469616C6F67756552656D6F746503023Q006F7303053Q00636C6F636B027Q004003043Q00722Q6F7403043Q0074696D652Q033Q00637478030D3Q004F6E436C69656E744576656E7403073Q00436F2Q6E65637403043Q007461736B03043Q0077616974029A5Q99A93F030A3Q00446973636F2Q6E65637402524Q007B00028Q0002000100014Q000200013Q00202Q00020002000100122Q000400026Q000500016Q00020005000200062Q0002000B00013Q0004393Q000B00010006A93Q000E000100010004393Q000E00012Q004700036Q00A1000400044Q0003000300033Q0012A5000300033Q0020160003000300042Q007700030001000200068F00040014000100010004393Q00140001001232000400054Q009C000500023Q00201600050005000600060C0005002400013Q0004393Q002400010012A5000500033Q00202D0005000500044Q0005000100024Q000600023Q00202Q0006000600074Q00050005000600062Q00050024000100040004393Q002400012Q0047000500014Q009C000600023Q0020160006000600082Q0003000500034Q004700056Q00A1000600073Q0020160008000200090020AC00080008000A000699000A3Q000100032Q00798Q00793Q00054Q00793Q00064Q006D0008000A00022Q0079000700083Q0006A90005004A000100010004393Q004A00010012A5000800033Q0020160008000800042Q00770008000100022Q007C0008000800030006490008004A000100040004393Q004A00010012A50008000B3Q0020A300080008000C00122Q0009000D6Q0008000200014Q000800023Q00202Q00080008000600062Q0008002E00013Q0004393Q002E00010012A5000800033Q00202D0008000800044Q0008000100024Q000900023Q00202Q0009000900074Q00080008000900062Q0008002E000100040004393Q002E00012Q0047000500014Q009C000800023Q0020160006000800080004393Q002E00010006140007004E00013Q0004393Q004E00010020AC00080007000E2Q00840008000200012Q0079000800054Q0079000900064Q0003000800034Q00013Q00013Q00017Q0002074Q009C00025Q00060C3Q0006000100020004393Q000600012Q0047000200014Q008C000200014Q008C000100024Q00013Q00017Q00063Q0003023Q006F7303053Q00636C6F636B025Q0020AC4003303Q0052657573696E67206361636865642053652Q6C436F6E6669726D20636F6E7465787420286E6F2074656C65706F727429030D3Q004469616C6F6775654576656E7403053Q007063612Q6C011D4Q009C00015Q0006A900010005000100010004393Q000500012Q004700016Q0051000100023Q0012A5000100013Q0020690001000100024Q0001000100024Q000200016Q000100010002000E2Q0003000E000100010004393Q000E00012Q004700016Q0051000100024Q009C000100023Q001232000200044Q00840001000200010006143Q001A00013Q0004393Q001A000100201600013Q00050006140001001A00013Q0004393Q001A00010012A5000100063Q00069900023Q000100012Q00798Q00840001000200012Q0047000100014Q0051000100024Q00013Q00013Q00013Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q004F70656E656400064Q00427Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00073Q00030E3Q0046696E6446697273744368696C6403093Q00506C61796572477569030A3Q004469616C6F6775655549030F3Q004469616C6F67756548616E646C65722Q033Q00497341030B3Q004C6F63616C53637269707403053Q007063612Q6C011D4Q002900015Q00202Q00010001000100122Q000300026Q00010003000200062Q00010007000100010004393Q000700012Q00013Q00013Q0020AC000200010001001232000400034Q006D0002000400020006A90002000D000100010004393Q000D00012Q00013Q00013Q0020AC000300020001001232000500044Q006D0003000500020006140003001C00013Q0004393Q001C00010020AC000400030005001232000600064Q006D0004000600020006140004001C00013Q0004393Q001C00010012A5000400073Q00069900053Q000100022Q00793Q00034Q00798Q00840004000200012Q00013Q00013Q00013Q00013Q0003083Q0044697361626C6564000A4Q009C8Q009C000100013Q0006140001000700013Q0004393Q000700012Q0047000100013Q0006A900010008000100010004393Q000800012Q004700015Q0010AD3Q000100012Q00013Q00017Q000D3Q00030E3Q0046696E6446697273744368696C6403063Q0053686172656403083Q005061636B6167657303043Q004B6E697403083Q00536572766963657303103Q0050726F78696D69747953657276696365030F3Q004469616C6F6775655365727669636503023Q00524603023Q005245030D3Q00466F7263654469616C6F67756503083Q004469616C6F677565030A3Q0052756E436F2Q6D616E64030D3Q004469616C6F6775654576656E7400474Q00757Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q0004393Q000900010020AC00013Q0001001232000300034Q006D0001000300020006870002000E000100010004393Q000E00010020AC000200010001001232000400044Q006D00020004000200068700030013000100020004393Q001300010020AC000300020001001232000500054Q006D00030005000200068700040018000100030004393Q001800010020AC000400030001001232000600064Q006D0004000600020006870005001D000100030004393Q001D00010020AC000500030001001232000700074Q006D00050007000200068700060022000100040004393Q002200010020AC000600040001001232000800084Q006D00060008000200068700070027000100050004393Q002700010020AC000700050001001232000900084Q006D0007000900020006870008002C000100050004393Q002C00010020AC000800050001001232000A00094Q006D0008000A00022Q003600093Q0004000687000A0032000100060004393Q003200010020AC000A00060001001232000C000A4Q006D000A000C00020010AD0009000A000A000687000A0038000100060004393Q003800010020AC000A00060001001232000C000B4Q006D000A000C00020010AD0009000B000A000687000A003E000100070004393Q003E00010020AC000A00070001001232000C000C4Q006D000A000C00020010AD0009000C000A000687000A0044000100080004393Q004400010020AC000A00080001001232000C000D4Q006D000A000C00020010AD0009000D000A2Q0051000900024Q00013Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403093Q0050726F78696D697479030A3Q0047722Q65647920436579000B4Q00757Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q0004393Q000900010020AC00013Q0001001232000300034Q006D0001000300022Q0051000100024Q00013Q00017Q00023Q0003063Q0055736572496403083Q00746F6E756D62657201164Q009C00015Q0006140001000500013Q0004393Q000500012Q009C00015Q0020160001000100010006A900010009000100010004393Q000900012Q004700026Q0051000200023Q00060C3Q000D000100010004393Q000D00012Q0047000200014Q0051000200023Q0012A5000200024Q007900036Q0093000200020002002Q0600020013000100010004393Q001300012Q006A00036Q0047000300014Q0051000300024Q00013Q00017Q00083Q0003043Q007479706503053Q007461626C6503063Q0072617767657403043Q004D697363030A3Q0045717569706D656E747303053Q00706169727303063Q00737472696E6703063Q006E756D62657201333Q0012A5000100014Q007900026Q009300010002000200265F00010007000100020004393Q000700012Q004700016Q0051000100023Q0012A5000100013Q001228000200036Q00035Q00122Q000400046Q000200046Q00013Q000200262Q00010017000100020004393Q001700010012A5000100013Q001225000200036Q00035Q00122Q000400056Q000200046Q00013Q000200262Q00010019000100020004393Q001900012Q0047000100014Q0051000100023Q0012A5000100064Q007900026Q00350001000200030004393Q002E00010012A5000600014Q0079000700044Q00930006000200020026040006002E000100070004393Q002E00010012A5000600014Q0079000700054Q009300060002000200265F0006002C000100080004393Q002C00010012A5000600014Q0079000700054Q00930006000200020026040006002E000100020004393Q002E00012Q0047000600014Q0051000600023Q00060A0001001D000100020004393Q001D00012Q004700016Q0051000100024Q00013Q00017Q00083Q0003053Q00706169727303043Q007479706503053Q007461626C6503063Q0072617767657403043Q004461746103093Q00496E76656E746F727903043Q005461677303063Q0055736572496401473Q0012A5000200014Q007900036Q00350002000200040004393Q004300010012A5000700024Q0079000800064Q009300070002000200260400070043000100030004393Q004300010012A5000700044Q004A000800063Q00122Q000900056Q00070009000200122Q000800026Q000900076Q00080002000200262Q00080037000100030004393Q003700010012A5000800044Q004A000900073Q00122Q000A00066Q0008000A000200122Q000900026Q000A00086Q00090002000200262Q00090037000100030004393Q003700010012A5000900044Q004A000A00063Q00122Q000B00076Q0009000B000200122Q000A00026Q000B00096Q000A0002000200262Q000A002D000100030004393Q002D00012Q009C000A5Q001221000B00046Q000C00093Q00122Q000D00086Q000B000D6Q000A3Q000200062Q000A002D00013Q0004393Q002D00012Q0051000700023Q0006A900090037000100010004393Q003700010006A900010037000100010004393Q003700012Q009C000A00014Q0079000B00084Q0093000A00020002000614000A003700013Q0004393Q003700012Q0079000100073Q0012A5000800044Q0079000900063Q001232000A00064Q006D0008000A00020006A900010043000100010004393Q004300012Q009C000900014Q0079000A00084Q00930009000200020006140009004300013Q0004393Q004300012Q0079000100063Q00060A00020004000100020004393Q000400012Q0051000100024Q00013Q00017Q00053Q0003043Q007479706503053Q00676574676303083Q0066756E6374696F6E03053Q007063612Q6C03053Q007461626C6500193Q0012A53Q00013Q0012A5000100024Q00933Q0002000200265F3Q0007000100030004393Q000700012Q00A18Q00513Q00023Q0012A53Q00043Q0012A5000100024Q0047000200014Q00923Q000200010006143Q001200013Q0004393Q001200010012A5000200014Q0079000300014Q009300020002000200265F00020014000100050004393Q001400012Q00A1000200024Q0051000200024Q009C00026Q0079000300014Q0070000200034Q001500026Q00013Q00017Q00063Q0003043Q007479706503053Q00646562756703053Q007461626C65030B3Q00676574726567697374727903083Q0066756E6374696F6E03053Q007063612Q6C001F3Q0012A53Q00013Q0012A5000100024Q00933Q000200020026043Q000B000100030004393Q000B00010012A53Q00013Q0012A5000100023Q0020160001000100042Q00933Q0002000200265F3Q000D000100050004393Q000D00012Q00A18Q00513Q00023Q0012A53Q00063Q0012A5000100023Q0020160001000100042Q00353Q000200010006143Q001800013Q0004393Q001800010012A5000200014Q0079000300014Q009300020002000200265F0002001A000100030004393Q001A00012Q00A1000200024Q0051000200024Q009C00026Q0079000300014Q0070000200034Q001500026Q00013Q00017Q00103Q00030E3Q0046696E6446697273744368696C64030D3Q005265706C696361436C69656E7403053Q007063612Q6C03073Q007265717569726503043Q007479706503053Q007461626C6503063Q0055736572496403083Q005265706C6963617303093Q005F7265706C6963617303083Q007265706C6963617303053Q00706169727303063Q0072617767657403043Q005461677303043Q004461746103083Q00746F6E756D62657203093Q00496E76656E746F727900624Q00297Q00206Q000100122Q000200028Q0002000200064Q0008000100010004393Q000800012Q00A1000100014Q0051000100023Q0012A5000100033Q0012A5000200044Q007900036Q00920001000300020006140001001300013Q0004393Q001300010012A5000300054Q0079000400024Q009300030002000200265F00030015000100060004393Q001500012Q00A1000300034Q0051000300024Q009C000300013Q0006140003001A00013Q0004393Q001A00012Q009C000300013Q0020160003000300070006A90003001E000100010004393Q001E00012Q00A1000400044Q0051000400024Q0036000400033Q00201600050002000800201600060002000900201600070002000A2Q00A60004000300010012A50005000B4Q0079000600044Q00350005000200070004393Q005D00010012A5000A00054Q0079000B00094Q0093000A00020002002604000A005D000100060004393Q005D00010012A5000A000B4Q0079000B00094Q0035000A0002000C0004393Q005B00010012A5000F00054Q00790010000E4Q0093000F00020002002604000F005B000100060004393Q005B00010012A5000F000C4Q000F0010000E3Q00122Q0011000D6Q000F0011000200122Q0010000C6Q0011000E3Q00122Q0012000E6Q00100012000200122Q001100056Q0012000F6Q00110002000200262Q0011005B000100060004393Q005B00010012A5001100054Q0079001200104Q00930011000200020026040011005B000100060004393Q005B00010012A50011000C4Q00790012000F3Q001232001300074Q006D001100130002002Q0600110052000100030004393Q005200010012A50012000F4Q0079001300114Q009300120002000200060C0012005B000100030004393Q005B00010012A5001200053Q0012250013000C6Q001400103Q00122Q001500106Q001300156Q00123Q000200262Q0012005B000100060004393Q005B00012Q0051001000023Q00060A000A0030000100020004393Q0030000100060A00050027000100020004393Q002700012Q00A1000500054Q0051000500024Q00013Q00017Q00033Q0003023Q00676303083Q00726567697374727903073Q007265706C696361001A4Q009C8Q00773Q000100020006143Q000700013Q0004393Q000700012Q007900015Q001232000200014Q0003000100034Q009C000100014Q00770001000100022Q00793Q00013Q0006143Q000F00013Q0004393Q000F00012Q007900015Q001232000200024Q0003000100034Q009C000100024Q00770001000100022Q00793Q00013Q0006143Q001700013Q0004393Q001700012Q007900015Q001232000200034Q0003000100034Q00A1000100024Q0003000100034Q00013Q00017Q000E3Q0003043Q007479706503053Q00676574676303083Q0066756E6374696F6E03053Q007063612Q6C03053Q007461626C6503063Q0055736572496403053Q00706169727303063Q0072617767657403053Q00546F6B656E03043Q005461677303043Q0044617461030C3Q00506C6179657253746174757303083Q00746F6E756D62657203083Q004D6F76656D656E7400593Q0012A53Q00013Q0012A5000100024Q00933Q0002000200265F3Q0007000100030004393Q000700012Q00A18Q00513Q00023Q0012A53Q00043Q0012A5000100024Q0047000200014Q00923Q000200010006143Q001200013Q0004393Q001200010012A5000200014Q0079000300014Q009300020002000200265F00020014000100050004393Q001400012Q00A1000200024Q0051000200024Q009C00025Q0006140002001900013Q0004393Q001900012Q009C00025Q0020160002000200060006A90002001D000100010004393Q001D00012Q00A1000300034Q0051000300023Q0012A5000300074Q0079000400014Q00350003000200050004393Q005400010012A5000800014Q0079000900074Q009300080002000200260400080054000100050004393Q005400010012A5000800084Q005A000900073Q00122Q000A00096Q0008000A000200122Q000900086Q000A00073Q00122Q000B000A6Q0009000B000200122Q000A00086Q000B00073Q00122Q000C000B6Q000A000C000200262Q000800540001000C0004393Q005400010012A5000B00014Q0079000C000A4Q0093000B00020002002604000B0054000100050004393Q005400010012A5000B00014Q0079000C00094Q0093000B00020002002604000B004B000100050004393Q004B00010012A5000B00084Q0079000C00093Q001232000D00064Q006D000B000D0002002Q06000B0049000100020004393Q004900010012A5000C000D4Q0079000D000B4Q0093000C0002000200060C000C0054000100020004393Q005400012Q0051000A00023Q0004393Q005400010012A5000B00013Q001225000C00086Q000D000A3Q00122Q000E000E6Q000C000E6Q000B3Q000200262Q000B0054000100050004393Q005400012Q0051000A00023Q00060A00030021000100020004393Q002100012Q00A1000300034Q0051000300024Q00013Q00017Q000D3Q00030E3Q0046696E6446697273744368696C6403093Q0050726F78696D697479030A3Q0047722Q656479204365792Q033Q0049734103053Q004D6F64656C030B3Q005072696D6172795061727403103Q0048756D616E6F6964522Q6F745061727403063Q00434672616D6503083Q004765745069766F7403083Q00426173655061727403083Q00506F736974696F6E030A3Q004C2Q6F6B566563746F72026Q00144000324Q00757Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q0004393Q000900010020AC00013Q0001001232000300034Q006D0001000300020006A90001000D000100010004393Q000D00012Q00A1000200024Q0051000200024Q00A1000200023Q0020AC000300010004001232000500054Q006D0003000500020006140003002200013Q0004393Q002200010020160003000100060006A900030019000100010004393Q001900010020AC000300010001001232000500074Q006D0003000500020006140003001E00013Q0004393Q001E000100201600040003000800068F00020021000100040004393Q002100010020AC0004000100092Q00930004000200022Q0079000200043Q0004393Q002800010020AC0003000100040012320005000A4Q006D0003000500020006140003002800013Q0004393Q002800010020160002000100080006140002002F00013Q0004393Q002F000100201600030002000B00201600040002000C00203E00040004000D2Q00980003000300042Q0051000300024Q00A1000300034Q0051000300024Q00013Q00017Q00053Q0003043Q007479706503093Q004661766F726974657303053Q007461626C6503053Q0070616972733Q01114Q003600015Q0006143Q000F00013Q0004393Q000F00010012A5000200013Q00201600033Q00022Q00930002000200020026040002000F000100030004393Q000F00010012A5000200043Q00201600033Q00022Q00350002000200040004393Q000D000100204400010005000500060A0002000C000100020004393Q000C00012Q0051000100024Q00013Q00017Q00053Q0003043Q007479706503063Q00737472696E6703053Q006D61746368034A3Q005E25782578257825782578257825782578252D2578257825782578252D2578257825782578252D2578257825782578252D257825782578257825782578257825782578257825782578240001103Q0012A5000100014Q007900026Q009300010002000200265F00010007000100020004393Q000700012Q004700016Q0051000100023Q0020AC00013Q0003001232000300044Q006D0001000300020026040001000D000100050004393Q000D00012Q006A00016Q0047000100014Q0051000100024Q00013Q00017Q00173Q0003283Q00706C617965722064617461206E6F7420666F756E6420286E6F206D6574686F6420776F726B65642903173Q00506C61796572206461746120666F756E64207669613A2003093Q00496E76656E746F727903223Q00696E76656E746F7279206E6F7420666F756E6420696E20706C617965722064617461028Q0003053Q00706169727303043Q007479706503063Q00737472696E6703063Q006E756D626572030D3Q00536B69704661766F726974657303043Q004D69736303053Q007461626C6503043Q004E616D6503083Q005175616E7469747903043Q004755494403043Q004F72657303053Q0052756E657303073Q005570677261646503043Q0054797065026Q00F03F03043Q006E6578740003173Q006E6F2073652Q6C61626C65206974656D7320666F756E6400984Q009C8Q00573Q000100010006A93Q0007000100010004393Q000700012Q00A1000200023Q001232000300014Q0003000200034Q009C000200013Q00128B000300026Q000400016Q0003000300044Q00020002000100202Q00023Q000300062Q00020012000100010004393Q001200012Q00A1000300033Q001232000400044Q0003000300034Q009C000300024Q004F00048Q0003000200024Q00045Q00122Q000500053Q00122Q000600066Q000700026Q00060002000800044Q003D00010012A5000B00074Q0079000C00094Q0093000B00020002002604000B003D000100080004393Q003D00010012A5000B00074Q0079000C000A4Q0093000B00020002002604000B003D000100090004393Q003D0001000E9B0005003D0001000A0004393Q003D00012Q009C000B00034Q0094000B000B00090006A9000B003D000100010004393Q003D00012Q009C000B00044Q0094000B000B00090006A9000B003D000100010004393Q003D00012Q009C000B00054Q0079000C00094Q0093000B000200020006A9000B003D000100010004393Q003D00012Q009C000B00063Q002016000B000B000A000614000B003B00013Q0004393Q003B00012Q0094000B000300090006A9000B003D000100010004393Q003D00012Q004D00040009000A2Q009800050005000A00060A0006001B000100020004393Q001B000100201600060002000B0012A5000700074Q0079000800064Q00930007000200020026040007008B0001000C0004393Q008B00010012A5000700064Q0079000800064Q00350007000200090004393Q008900010012A5000C00074Q0079000D000B4Q0093000C00020002002604000C00890001000C0004393Q00890001002016000C000B000D002016000D000B000E002016000E000B000F2Q0047000F5Q000614000C007000013Q0004393Q00700001000614000D007000013Q0004393Q007000010012A5001000074Q00790011000D4Q009300100002000200260400100070000100090004393Q00700001000E9B000500700001000D0004393Q007000012Q009C001000044Q009400100010000C0006140010007000013Q0004393Q007000012Q009C001000063Q00201600100010000A0006140010006800013Q0004393Q006800012Q009400100003000C0006A900100070000100010004393Q007000012Q009400100004000C0006A90010006C000100010004393Q006C0001001232001000054Q009800100010000D2Q004D0004000C00102Q009800050005000D2Q0047000F00013Q0006A9000F0089000100010004393Q00890001000614000E008900013Q0004393Q008900010020160010000B00100006A90010007E000100010004393Q007E00010020160010000B00110006A90010007E000100010004393Q007E00010020160010000B00120006A90010007E000100010004393Q007E00010020160010000B00130006A900100089000100010004393Q008900012Q009C001100063Q00201600110011000A0006140011008700013Q0004393Q008700012Q009400110003000E0006A900110089000100010004393Q008900010020440004000E001400209600050005001400060A00070049000100020004393Q004900010012A5000700154Q0079000800044Q009300070002000200260400070093000100160004393Q009300012Q00A1000700073Q001232000800174Q0003000700034Q0079000700044Q00A1000800084Q0079000900054Q006C000700024Q00013Q00017Q00043Q00030E3Q0046696E6446697273744368696C6403063Q004C6976696E6703043Q004E616D6503093Q00436861726163746572000F4Q00627Q00206Q000100122Q000200028Q0002000200064Q000B00013Q0004393Q000B00010020AC00013Q00012Q009C000300013Q0020160003000300032Q0070000100034Q001500016Q009C000100013Q0020160001000100042Q0051000100024Q00013Q00017Q00023Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727401073Q0006870001000500013Q0004393Q000500010020AC00013Q0001001232000300024Q006D0001000300022Q0051000100024Q00013Q00017Q00103Q0003083Q00496E7374616E63652Q033Q006E657703043Q005061727403043Q004E616D6503103Q0053652Q6C4D6F64756C6543617270657403043Q0053697A6503073Q00566563746F7233026Q001840026Q00E03F030C3Q005472616E73706172656E6379026Q00F03F03083Q00416E63686F7265642Q01030A3Q0043616E436F2Q6C696465010003063Q00506172656E74001D4Q009C7Q0006143Q000400013Q0004393Q000400012Q00013Q00013Q0012A53Q00013Q00201E5Q000200122Q000100038Q000200029Q009Q0000304Q000400059Q0000122Q000100073Q00202Q00010001000200122Q000200083Q00122Q000300093Q00122Q000400086Q00010004000200104Q000600019Q0000304Q000A000B9Q0000304Q000C000D9Q0000304Q000E000F9Q004Q000100013Q00104Q001000016Q00017Q00043Q0003063Q00506172656E7403063Q00434672616D652Q033Q006E6577028Q0001144Q009C00015Q0006140001000800013Q0004393Q000800010006143Q000800013Q0004393Q0008000100201600013Q00010006A900010009000100010004393Q000900012Q00013Q00014Q009C00015Q00209500023Q000200122Q000300023Q00202Q00030003000300122Q000400046Q000500013Q00122Q000600046Q0003000600024Q00020002000300102Q0001000200026Q00017Q00013Q0003073Q0044657374726F7900094Q009C7Q0006143Q000800013Q0004393Q000800012Q009C7Q0020AC5Q00012Q00843Q000200012Q00A18Q008C8Q00013Q00017Q00113Q00030A3Q00446973636F2Q6E656374030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030D3Q00506C6174666F726D5374616E64010003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964652Q0103073Q0044657374726F7903103Q0053652Q6C426F6479506F736974696F6E00504Q00478Q008C8Q009C3Q00013Q0006143Q000A00013Q0004393Q000A00012Q009C3Q00013Q0020AC5Q00012Q00843Q000200012Q00A18Q008C3Q00014Q009C3Q00023Q0006143Q001200013Q0004393Q001200012Q009C3Q00023Q0020AC5Q00012Q00843Q000200012Q00A18Q008C3Q00024Q009C3Q00034Q00773Q000100020006143Q003700013Q0004393Q003700012Q009C000100044Q007100028Q00010002000200202Q00023Q000200122Q000400036Q00020004000200062Q0001002400013Q0004393Q002400010012A5000300053Q00207A00030003000600102Q00010004000300122Q000300053Q00202Q00030003000600102Q0001000700030006140002002A00013Q0004393Q002A00010020160003000200080006140003002A00013Q0004393Q002A00010030590002000800090012A50003000A3Q0020AC00043Q000B2Q0019000400054Q006400033Q00050004393Q003500010020AC00080007000C001232000A000D4Q006D0008000A00020006140008003500013Q0004393Q003500010030590007000E000F00060A0003002F000100020004393Q002F00012Q009C000100053Q0006140001003F00013Q0004393Q003F00012Q009C000100053Q0020AC0001000100102Q00840001000200012Q00A1000100014Q008C000100053Q0006143Q004D00013Q0004393Q004D00012Q009C000100044Q007900026Q00930001000200020006140001004D00013Q0004393Q004D00010020AC000200010002001232000400114Q006D0002000400020006140002004D00013Q0004393Q004D00010020AC0003000200102Q00840003000200012Q009C000100064Q00180001000100012Q00013Q00017Q00163Q0003043Q007461736B03043Q0077616974029A5Q99B93F030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403213Q00466C79546F206661696C65643A20436861726163746572206E6F7420666F756E64030D3Q00506C6174666F726D5374616E642Q0103163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F6369747903053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964650100030B3Q00466C79696E6720746F3A202Q033Q004E504303093Q0048656172746265617403073Q00436F2Q6E65637402564Q009C00025Q0006140002000900013Q0004393Q000900012Q009C000200014Q007F00020001000100122Q000200013Q00202Q00020002000200122Q000300036Q0002000200012Q009C000200024Q003A0002000100024Q000300036Q000400026Q00030002000200062Q00040013000100020004393Q001300010020AC000400020004001232000600054Q006D0004000600020006140003001700013Q0004393Q001700010006A90004001B000100010004393Q001B00012Q009C000500043Q001232000600064Q00840005000200012Q00013Q00013Q0030590004000700080012800005000A3Q00202Q00050005000B00102Q00030009000500122Q0005000A3Q00202Q00050005000B00102Q0003000C000500128E0005000D3Q00202Q00060002000E4Q000600076Q00053Q000700044Q002D00010020AC000A0009000F001232000C00104Q006D000A000C0002000614000A002D00013Q0004393Q002D000100305900090011001200060A00050027000100020004393Q002700012Q0047000500014Q00A000058Q000500056Q0005000100014Q000500066Q000600036Q0005000200014Q000500043Q00122Q000600133Q00062Q0007003B000100010004393Q003B0001001232000700144Q00720006000600072Q00840005000200012Q009C000500083Q0020160005000500150020AC00050005001600069900073Q000100022Q009C8Q009C3Q00024Q00880005000700024Q000500076Q000500083Q00202Q00050005001500202Q000500050016000699000700010001000A2Q009C8Q009C3Q00024Q009C3Q00034Q009C3Q00064Q00798Q009C3Q000A4Q009C3Q00044Q009C3Q00014Q009C3Q000B4Q009C3Q000C4Q006D0005000700022Q008C000500094Q00013Q00013Q00023Q00063Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465012Q001A4Q009C7Q0006A93Q0004000100010004393Q000400012Q00013Q00014Q009C3Q00014Q00773Q000100020006A93Q0009000100010004393Q000900012Q00013Q00013Q0012A5000100013Q0020AC00023Q00022Q0019000200034Q006400013Q00030004393Q001700010020AC000600050003001232000800044Q006D0006000800020006140006001700013Q0004393Q001700010020160006000500050006140006001700013Q0004393Q0017000100305900050005000600060A0001000E000100020004393Q000E00012Q00013Q00017Q00263Q00030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030D3Q00506C6174666F726D5374616E642Q0103083Q00506F736974696F6E03093Q004D61676E697475646503163Q00412Q72697665642061742064657374696E6174696F6E026Q11913F03043Q00556E697403043Q006D6174682Q033Q006D696E03083Q00496E7374616E63652Q033Q006E657703083Q00426F64794779726F03093Q004D6178546F7271756503073Q00566563746F7233024Q00652QCD4103013Q0050025Q0088C34003013Q0044026Q00594003063Q00506172656E7403013Q005803013Q005903013Q005A029A5Q99B93F03063Q00434672616D6503063Q006C2Q6F6B417403103Q0053652Q6C426F6479506F736974696F6E030C3Q00426F6479506F736974696F6E03043Q004E616D6503083Q004D6178466F726365024Q0080842E41025Q006AE840025Q00408F4003163Q00412Q73656D626C794C696E65617256656C6F6369747903043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479017F4Q009C00015Q0006A900010004000100010004393Q000400012Q00013Q00014Q009C000100014Q003A0001000100024Q000200026Q000300016Q00020002000200062Q0003000E000100010004393Q000E00010020AC000300010001001232000500024Q006D0003000500020006140002001200013Q0004393Q001200010006A900030013000100010004393Q001300012Q00013Q00014Q009C000400034Q0079000500024Q00840004000200010020160004000300030006A90004001A000100010004393Q001A00010030590003000300040020160004000200052Q0023000500046Q00050005000400202Q0006000500064Q000700053Q00062Q00060027000100070004393Q002700012Q009C000700063Q00126B000800076Q0007000200014Q000700076Q0007000100016Q00014Q009C000700083Q00068F0008002B00013Q0004393Q002B0001001232000800084Q002C00070007000800208500080005000900122Q0009000A3Q00202Q00090009000B4Q000A00076Q000B00066Q0009000B00024Q000A000800094Q000A0004000A4Q000B00093Q00062Q000B004A000100010004393Q004A00010012A5000B000C3Q00202B000B000B000D00122Q000C000E6Q000B000200024Q000B00096Q000B00093Q00122Q000C00103Q00202Q000C000C000D00122Q000D00113Q00122Q000E00113Q00122Q000F00116Q000C000F000200102Q000B000F000C4Q000B00093Q00302Q000B001200134Q000B00093Q00302Q000B001400154Q000B00093Q00102Q000B001600020012A5000B00103Q002078000B000B000D4Q000C00043Q00202Q000C000C001700202Q000D000A00184Q000E00043Q00202Q000E000E00194Q000B000E00024Q000C000B000A00202Q000C000C0006000E2Q001A005D0001000C0004393Q005D00012Q009C000D00093Q001266000E001B3Q00202Q000E000E001C4Q000F000A6Q0010000B6Q000E0010000200102Q000D001B000E0020AC000D00020001001232000F001D4Q006D000D000F00020006A9000D0072000100010004393Q007200010012A5000E000C3Q002058000E000E000D00122Q000F001E6Q000E000200024Q000D000E3Q00302Q000D001F001D00122Q000E00103Q00202Q000E000E000D00122Q000F00213Q00122Q001000213Q00122Q001100216Q000E0011000200102Q000D0020000E00302Q000D0012002200302Q000D0014002300102Q000D001600020010AD000D0005000A00122Q000E001B3Q00202Q000E000E000D4Q000F000A6Q000E0002000200102Q0002001B000E00122Q000E00103Q00202Q000E000E002500102Q00020024000E00122Q000E00103Q00202Q000E000E002500102Q00020026000E6Q00017Q00103Q00030D3Q00466F7263654469616C6F67756503083Q004469616C6F67756503053Q007063612Q6C010003103Q0053652Q6C4469616C6F6775654D697363026Q00F83F030D3Q004469616C6F6775654576656E7403043Q007461736B03043Q0077616974026Q00E03F00030F3Q0053652Q6C436F6E6669726D4D697363027Q004003383Q005761726E696E673A2053652Q6C436F6E6669726D4D697363206E6F74206F627365727665642C20636F6E74696E75696E6720616E7977617903023Q006F7303053Q00636C6F636B02743Q0006143Q000A00013Q0004393Q000A000100201600023Q00010006140002000A00013Q0004393Q000A000100201600023Q00020006140002000A00013Q0004393Q000A00010006A90001000C000100010004393Q000C00012Q004700026Q0051000200023Q0012A5000200033Q00069900033Q000100022Q00798Q00793Q00014Q00350002000200030006140002002600013Q0004393Q0026000100265F00030026000100040004393Q002600012Q009C00045Q001232000500053Q001232000600064Q006D0004000600020006140004002600013Q0004393Q0026000100201600053Q00070006140005002600013Q0004393Q002600010012A5000500033Q00069900060001000100012Q00798Q00840005000200010012A5000500033Q00069900060002000100012Q00798Q00840005000200012Q004700045Q0012A5000500033Q00069900060003000100022Q00798Q00793Q00014Q00350005000200062Q0079000300064Q0079000200053Q0006140002003300013Q0004393Q0033000100265F00030033000100040004393Q003300012Q0047000400013Q0006A900040043000100010004393Q004300010012A5000500083Q0020160005000500090012320006000A4Q00840005000200010012A5000500033Q00069900060004000100022Q00798Q00793Q00014Q00350005000200060006140005004300013Q0004393Q0043000100265F00060043000100040004393Q004300012Q0047000400013Q0006A90004004A000100010004393Q004A00010006140002004A00013Q0004393Q004A00010026040003004A0001000B0004393Q004A00012Q0047000400013Q0006A90004004E000100010004393Q004E00012Q004700056Q0051000500024Q009C00055Q0012320006000C3Q0012320007000D4Q00920005000700060006A90005005E000100010004393Q005E00010012A5000700083Q00204000070007000900122Q0008000A6Q0007000200014Q00075Q00122Q0008000C3Q00122Q0009000D6Q0007000900084Q000600086Q000500073Q0006A900050063000100010004393Q006300012Q009C000700013Q0012320008000E4Q00840007000200010006140006006A00013Q0004393Q006A00012Q008C000600023Q0012A50007000F3Q0020160007000700102Q00770007000100022Q008C000700033Q00201600073Q00070006140007007100013Q0004393Q007100010012A5000700033Q00069900080005000100012Q00798Q00840007000200012Q0047000700014Q0051000700024Q00013Q00013Q00063Q00023Q0003083Q004469616C6F677565030C3Q00496E766F6B6553657276657200074Q00677Q00206Q000100206Q00024Q000200018Q00029Q008Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q004F70656E656400064Q00427Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q00436C6F73656400064Q00427Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q00466F7263654469616C6F677565030C3Q00496E766F6B65536572766572030F3Q0053652Q6C436F6E6669726D4D69736300084Q00897Q00206Q000100206Q00024Q000200013Q00122Q000300038Q00039Q008Q00017Q00033Q00030D3Q00466F7263654469616C6F677565030C3Q00496E766F6B65536572766572030F3Q0053652Q6C436F6E6669726D4D69736300084Q00897Q00206Q000100206Q00024Q000200013Q00122Q000300038Q00039Q008Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q004F70656E656400064Q00427Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q000D3Q00030E3Q0046696E6446697273744368696C6403063Q00537461747573030F3Q0044697361626C654261636B7061636B03283Q0052656D6F76696E672044697361626C654261636B7061636B207461672066726F6D2053746174757303053Q007063612Q6C030D3Q004469616C6F6775654576656E7403093Q00506C61796572477569030A3Q004469616C6F677565554903053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q0047756942752Q746F6E03113Q00526573706F6E736542692Q6C626F617264014D3Q0006A93Q0003000100010004393Q000300012Q00013Q00014Q009C00016Q00770001000100020006140001001900013Q0004393Q001900010020AC000200010001001232000400024Q006D0002000400020006140002001900013Q0004393Q001900010020AC000300020001001232000500034Q006D0003000500020006140003001800013Q0004393Q001800012Q009C000400013Q001232000500044Q00840004000200010012A5000400053Q00069900053Q000100012Q00793Q00034Q00840004000200012Q002E00035Q00201600023Q00060006140002002000013Q0004393Q002000010012A5000200053Q00069900030001000100012Q00798Q00840002000200010012A5000200053Q00069900030002000100012Q009C3Q00024Q009E0002000200014Q000200033Q00202Q00020002000100122Q000400076Q00020004000200062Q0002004C00013Q0004393Q004C00010020AC000300020001001232000500084Q006D0003000500020006140003004000013Q0004393Q004000010012A5000400093Q0020AC00050003000A2Q0019000500064Q006400043Q00060004393Q003E00010020AC00090008000B001232000B000C4Q006D0009000B00020006140009003D00013Q0004393Q003D00010012A5000900053Q000699000A0003000100012Q00793Q00084Q00840009000200012Q002E00075Q00060A00040034000100020004393Q0034000100068700040045000100030004393Q004500010020AC0004000300010012320006000D4Q006D0004000600020006140004004B00013Q0004393Q004B00010012A5000500053Q00069900060004000100012Q00793Q00044Q00840005000200012Q002E00036Q00013Q00013Q00053Q00013Q0003073Q0044657374726F7900044Q009C7Q0020AC5Q00012Q00843Q000200012Q00013Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q00436C6F73656400064Q00427Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030E3Q0053656C65637465644F626A65637400030E3Q00436C65617253656C656374696F6E000A4Q00437Q00304Q000100029Q0000206Q000300064Q000900013Q0004393Q000900012Q009C7Q0020AC5Q00032Q00843Q000200012Q00013Q00017Q00033Q0003073Q0056697369626C650100030C3Q00496E74657261637461626C6500054Q000D7Q00304Q000100029Q0000304Q000300026Q00017Q00023Q0003073Q0056697369626C65012Q00034Q009C7Q0030593Q000100022Q00013Q00017Q00533Q0003093Q004175746F2053652Q6C03083Q004E6F206974656D73027Q004003123Q004261736B6574206275696C7420776974682003063Q00206974656D73030A3Q0052756E436F2Q6D616E64030D3Q00466F7263654469616C6F67756503083Q004469616C6F67756503113Q0052656D6F746573206E6F7420666F756E64026Q00084003183Q004E50432047722Q65647920436579206E6F7420666F756E64030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403063Q00434672616D6503093Q0057616C6B53702Q6564026Q00304003093Q004A756D70506F776572026Q004940030D3Q00666F72636554656C65706F7274030A3Q006E6F54656C65706F7274031C3Q0053652Q6C4F6E63652063612Q6C65643A206E6F54656C65706F72743D03083Q00746F737472696E6703103Q002C20666F72636554656C65706F72743D03303Q005573696E672063616368656420636F6E74657874202D20736B692Q70696E67204F70656E53652Q6C4469616C6F67756503133Q004F70656E696E67206469616C6F6775653Q2E030D3Q006469616C6F674F70656E65643D030D3Q002C206E6F54656C65706F72743D03153Q002C20486173496E697469616C697A656453652Q6C3D03143Q004E6F54656C65706F72744166746572466972737403373Q0052657475726E696E67206561726C79202D206469616C6F67206E6F74206F70656E656420616E64206E6F54656C65706F7274206D6F646503353Q004469616C6F6720746964616B20646170617420646962756B612074616E70612074656C65706F72742E2044656B617469204E50432E03163Q004E504320706F736974696F6E206E6F7420666F756E6403133Q00436861726163746572206E6F7420666F756E64031C3Q0054656C65706F7274696E6720746F2047722Q656479204365793Q2E2Q033Q006E657703163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F6369747903043Q007461736B03043Q0077616974029A5Q99B93F03173Q004661696C656420746F206F70656E206469616C6F67756503223Q0053656E64696E672053652Q6C436F6E6669726D2077697468206261736B65743Q2E03053Q007063612Q6C010003133Q00436C6F73696E67206469616C6F6775653Q2E03103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E030B3Q005072696D61727950617274028Q0003323Q0054656C65706F7274696E67206177617920746F207472692Q676572206469616C6F677565206175746F2D636C6F73653Q2E026Q33F33F03213Q0052657475726E696E6720746F206F726967696E616C20706F736974696F6E3Q2E03043Q007469636B03063Q00737472696E6703063Q00666F726D6174030D3Q00536F6C64202564206974656D73030D3Q0053652Q6C2053552Q43452Q5321030B3Q0053652Q6C206661696C6564030B3Q0053652Q6C204641494C454403063Q0053746174757303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q00422Q6F6C56616C756503043Q004E616D65031B3Q0052656D6F76696E672053746174757320422Q6F6C56616C75653A20030B3Q004E756D62657256616C756503053Q006C6F77657203043Q0066696E64030C3Q0064617368632Q6F6C646F776E03253Q00526573652Q74696E67206461736820632Q6F6C646F776E204E756D62657256616C75653A202Q033Q00203D2003053Q0056616C7565030D3Q00506C6174666F726D5374616E642Q033Q0053697403163Q0057616C6B53702Q656420726573746F72656420746F2003163Q004A756D70506F77657220726573746F72656420746F2003083Q00416E63686F726564031B3Q0048756D616E6F6964522Q6F745061727420756E616E63686F72656403053Q0064656C6179026Q00E03F0113023Q009C00015Q0006140001000500013Q0004393Q000500012Q004700016Q0051000100024Q0047000100014Q002400018Q000100016Q000200016Q0001000200014Q000100026Q00010001000300062Q0001001C000100010004393Q001C00012Q004700046Q008C00046Q009C000400033Q001232000500013Q00068F00060015000100020004393Q00150001001232000600023Q001232000700034Q00740004000700014Q000400016Q00058Q0004000200014Q00048Q000400024Q009C000400043Q00120E000500046Q000600033Q00122Q000700056Q0005000500074Q0004000200014Q000400056Q00040001000200202Q00050004000600062Q0005002D00013Q0004393Q002D00010020160005000400070006140005002D00013Q0004393Q002D00010020160005000400080006A900050038000100010004393Q003800012Q004700056Q000200058Q000500033Q00122Q000600013Q00122Q000700093Q00122Q0008000A6Q0005000800014Q000500016Q00068Q0005000200016Q00014Q009C000500064Q00770005000100020006A900050047000100010004393Q004700012Q004700066Q000200068Q000600033Q00122Q000700013Q00122Q0008000B3Q00122Q0009000A6Q0006000900014Q000600016Q00078Q0006000200016Q00014Q009C000600074Q003A0006000100024Q000700086Q000800066Q00070002000200062Q00080051000100060004393Q005100010020AC00080006000C001232000A000D4Q006D0008000A000200068700090054000100070004393Q0054000100201600090007000E2Q0047000A5Q0006140008005A00013Q0004393Q005A0001002016000B0008000F0006A9000B005B000100010004393Q005B0001001232000B00103Q0006140008006000013Q0004393Q00600001002016000C000800110006A9000C0061000100010004393Q00610001001232000C00123Q000687000D006400013Q0004393Q00640001002016000D3Q0013000687000E006700013Q0004393Q00670001002016000E3Q00142Q009C000F00043Q00128D001000153Q00122Q001100166Q0012000E6Q00110002000200122Q001200173Q00122Q001300166Q0014000D6Q0013000200024Q0010001000134Q000F0002000100062Q000D007600013Q0004393Q007600012Q0047000F6Q008C000F00094Q0047000F6Q00110010000A6Q001100046Q0010000200024Q000F00103Q00062Q000F008100013Q0004393Q008100012Q009C001000043Q001232001100184Q00840010000200010004393Q008900012Q009C001000043Q001213001100196Q0010000200014Q0010000B6Q001100046Q001200056Q0010001200024Q000F00104Q009C001000043Q0012560011001A3Q00122Q001200166Q0013000F6Q00120002000200122Q0013001B3Q00122Q001400166Q0015000E6Q00140002000200122Q0015001C3Q00122Q001600166Q001700096Q0016000200024Q0011001100164Q00100002000100062Q000F00B4000100010004393Q00B400010006A9000E00A3000100010004393Q00A300012Q009C001000093Q000614001000B400013Q0004393Q00B400012Q009C0010000C3Q00201600100010001D000614001000B400013Q0004393Q00B400012Q009C001000043Q00124E0011001E6Q0010000200014Q00108Q00105Q00062Q000E00AF000100010004393Q00AF00012Q009C001000033Q001232001100013Q0012320012001F3Q0012320013000A4Q00830010001300012Q009C001000014Q004700116Q00840010000200012Q004700106Q0051001000023Q0006A9000F00EF000100010004393Q00EF00010006A9000E00EF000100010004393Q00EF00012Q009C0010000D4Q00770010000100020006A9001000C7000100010004393Q00C700012Q004700116Q000200118Q001100033Q00122Q001200013Q00122Q001300203Q00122Q0014000A6Q0011001400014Q001100016Q00128Q0011000200016Q00013Q0006A9000700D4000100010004393Q00D400012Q004700116Q000200118Q001100033Q00122Q001200013Q00122Q001300213Q00122Q0014000A6Q0011001400014Q001100016Q00128Q0011000200016Q00014Q009C001100043Q00123D001200226Q0011000200014Q000A00013Q00122Q0011000E3Q00202Q0011001100234Q001200106Q00110002000200102Q0007000E001100122Q001100253Q00202Q00110011002600102Q00070024001100122Q001100253Q00202Q00110011002600102Q00070027001100122Q001100283Q00202Q00110011002900122Q0012002A6Q0011000200014Q001100043Q00122Q001200196Q0011000200014Q0011000B6Q001200046Q001300056Q0011001300024Q000F00113Q0006A9000F000B2Q0100010004393Q000B2Q01000614000A00FE00013Q0004393Q00FE0001000614000900FE00013Q0004393Q00FE0001000614000700FE00013Q0004393Q00FE00010010AD0007000E0009001280001000253Q00202Q00100010002600102Q00070024001000122Q001000253Q00202Q00100010002600102Q0007002700102Q004700106Q0097001000096Q00108Q00108Q001000033Q00122Q001100013Q00122Q0012002B3Q00122Q0013000A6Q0010001300014Q001000016Q00118Q0010000200016Q00014Q0047001000014Q0054001000096Q001000043Q00122Q0011002C6Q0010000200014Q00105Q00122Q0011002D3Q00069900123Q000100022Q00793Q00044Q00793Q00014Q00350011000200120006140011001B2Q013Q0004393Q001B2Q0100265F0012001B2Q01002E0004393Q001B2Q012Q0047001000013Q0012A5001300283Q00202700130013002900122Q0014002A6Q0013000200014Q001300043Q00122Q0014002F6Q0013000200014Q0013000E6Q001400046Q0013000200014Q001300016Q00148Q00130002000100062Q000E00552Q0100010004393Q00552Q01000614000700552Q013Q0004393Q00552Q01000614000500552Q013Q0004393Q00552Q01002016001300050030000614001300352Q013Q0004393Q00352Q010020160013000500300020160013001300310006A90013003A2Q0100010004393Q003A2Q010020160013000500320006140013003A2Q013Q0004393Q003A2Q01002016001300050032002016001300130031000614001300552Q013Q0004393Q00552Q010012A5001400253Q00203700140014002300122Q001500123Q00122Q001600333Q00122Q001700126Q0014001700024Q0014001300144Q001500043Q00122Q001600346Q00150002000100122Q0015000E3Q00202Q0015001500234Q001600146Q00150002000200102Q0007000E001500122Q001500253Q00202Q00150015002600102Q00070024001500122Q001500253Q00202Q00150015002600102Q00070027001500122Q001500283Q00202Q00150015002900122Q001600356Q001500020001000614000A00692Q013Q0004393Q00692Q01000614000900692Q013Q0004393Q00692Q01000614000700692Q013Q0004393Q00692Q012Q009C001300043Q0012AE001400366Q00130002000100102Q0007000E000900122Q001300253Q00202Q00130013002600102Q00070024001300122Q001300253Q00202Q00130013002600102Q00070027001300122Q001300283Q00202Q00130013002900122Q0014002A6Q0013000200010006140010007B2Q013Q0004393Q007B2Q010012A5001300374Q003C0013000100024Q0013000F6Q001300033Q00122Q001400013Q00122Q001500383Q00202Q00150015003900122Q0016003A6Q001700036Q00150017000200122Q001600036Q0013001600014Q001300043Q00122Q0014003B6Q00130002000100044Q00832Q012Q009C001300033Q00121F001400013Q00122Q0015003C3Q00122Q0016000A6Q0013001600014Q001300043Q00122Q0014003D6Q0013000200012Q004700136Q008100138Q001300106Q001400076Q00140001000200062Q0015008D2Q0100140004393Q008D2Q010020AC00150014000C0012320017000D4Q006D001500170002000687001600922Q0100140004393Q00922Q010020AC00160014000C001232001800304Q006D0016001800020006140015001102013Q0004393Q001102010020AC00170014000C0012320019003E4Q006D001700190002000614001700CE2Q013Q0004393Q00CE2Q010012A50018003F3Q0020AC0019001700402Q00190019001A4Q006400183Q001A0004393Q00CC2Q010020AC001D001C0041001232001F00424Q006D001D001F0002000614001D00B12Q013Q0004393Q00B12Q012Q009C001D00103Q002016001E001C00432Q0093001D00020002000614001D00B12Q013Q0004393Q00B12Q012Q009C001D00043Q0012A4001E00443Q00202Q001F001C00434Q001E001E001F4Q001D0002000100122Q001D002D3Q000699001E0001000100012Q00793Q001C4Q0084001D000200010020AC001D001C0041001232001F00454Q006D001D001F0002000614001D00CB2Q013Q0004393Q00CB2Q01002016001D001C0043002010001D001D00464Q001D0002000200202Q001D001D004700122Q001F00486Q001D001F000200062Q001D00CB2Q013Q0004393Q00CB2Q012Q009C001D00043Q00121D001E00493Q00202Q001F001C004300122Q0020004A3Q00122Q002100163Q00202Q0022001C004B4Q0021000200024Q001E001E00214Q001D0002000100122Q001D002D3Q000699001E0002000100012Q00793Q001C4Q0084001D000200012Q002E001B5Q00060A0018009E2Q0100020004393Q009E2Q010030590015004C002E0030590015004D002E00201600180015000F00265F001800D62Q0100330004393Q00D62Q0100201600180015000F000649001800DC2Q01000B0004393Q00DC2Q010010AD0015000F000B2Q006F001800043Q00122Q0019004E6Q001A000B6Q00190019001A4Q00180002000100201600180015001100265F001800E22Q0100330004393Q00E22Q01002016001800150011000649001800E82Q01000C0004393Q00E82Q010010AD00150011000C2Q006F001800043Q00122Q0019004F6Q001A000C6Q00190019001A4Q001800020001000614001600F12Q013Q0004393Q00F12Q01002016001800160050000614001800F12Q013Q0004393Q00F12Q0100305900160050002E2Q009C001800043Q001232001900514Q00840018000200010012A50018002D3Q00069900190003000100012Q00793Q00154Q00840018000200010012A50018002D3Q00069900190004000100032Q009C3Q00114Q009C3Q00124Q009C3Q00044Q00840018000200010012A50018002D3Q00069900190005000100032Q009C3Q00134Q009C3Q00124Q009C3Q00044Q00840018000200010012A50018002D3Q00069900190006000100022Q009C3Q00134Q009C3Q00044Q00840018000200010012A5001800283Q002016001800180052001232001900533Q000699001A0007000100062Q00793Q00154Q00793Q000B4Q00793Q000C4Q00793Q00164Q009C3Q00074Q009C3Q00104Q00830018001A00012Q0051001300024Q00013Q00013Q00083Q00043Q00030A3Q0052756E436F2Q6D616E64030C3Q00496E766F6B65536572766572030B3Q0053652Q6C436F6E6669726D03063Q004261736B6574000A4Q00AB7Q00206Q000100206Q000200122Q000200036Q00033Q00014Q000400013Q00102Q0003000400046Q00039Q008Q00017Q00013Q0003073Q0044657374726F7900044Q009C7Q0020AC5Q00012Q00843Q000200012Q00013Q00017Q00023Q0003053Q0056616C7565029Q00034Q009C7Q0030593Q000100022Q00013Q00017Q00043Q00030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503073Q0052752Q6E696E6700074Q009A7Q00206Q000100122Q000200023Q00202Q00020002000300202Q0002000200046Q000200016Q00017Q00023Q0003083Q004D6F76656D656E7403243Q005265736574206461736820632Q6F6C646F776E2076696120506C6179657253746174757300104Q009C8Q00773Q000100020006143Q000F00013Q0004393Q000F000100201600013Q00010006140001000F00013Q0004393Q000F00012Q009C000100013Q00201600023Q00012Q00930001000200020006140001000F00013Q0004393Q000F00012Q009C000100023Q001232000200024Q00840001000200012Q00013Q00017Q000F3Q00030E3Q0046696E6446697273744368696C6403063Q0053686172656403083Q005061636B6167657303043Q004B6E697403073Q0072657175697265030D3Q00476574436F6E74726F2Q6C657203103Q00506C61796572436F6E74726F2Q6C657203063Q0053746174757303043Q004461746103083Q004D6F76656D656E7403383Q00526573657420506C61796572436F6E74726F2Q6C65722E5374617475732E446174612E4D6F76656D656E742E44617368432Q6F6C646F776E03133Q00436861726163746572436F6E74726F2Q6C657203093Q00432Q6F6C646F776E7303123Q005374616D696E61496E746572666163654364029Q003A4Q00757Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q0004393Q000900010020AC00013Q0001001232000300034Q006D0001000300020006870002000E000100010004393Q000E00010020AC000200010001001232000400044Q006D0002000400020006140002003900013Q0004393Q003900010012A5000300054Q0079000400024Q00930003000200020020160004000300060006140004003900013Q0004393Q00390001002016000400030006001232000500074Q00930004000200020006140004002F00013Q0004393Q002F00010020160005000400080006140005002F00013Q0004393Q002F00010020160005000400080020160006000500090006140006002F00013Q0004393Q002F000100201600060005000900201600060006000A0006140006002F00013Q0004393Q002F00012Q009C000600013Q00201600070005000900201600070007000A2Q00930006000200020006140006002F00013Q0004393Q002F00012Q009C000600023Q0012320007000B4Q00840006000200010020160005000300060012320006000C4Q00930005000200020006140005003900013Q0004393Q0039000100201600060005000D0006140006003900013Q0004393Q0039000100201600060005000D0030590006000E000F2Q00013Q00017Q000A3Q0003073Q007265717569726503063Q00536861726564030B3Q00496E707574416374696F6E03063Q00556E6C6F636B03043Q00456E756D03073Q004B6579436F646503013Q0051031E3Q00556E6C6F636B65642051206B65792076696120496E707574416374696F6E03093Q00556E6C6F636B412Q6C03053Q00436C656172001D3Q00123B3Q00016Q00015Q00202Q00010001000200202Q0001000100036Q0002000200064Q001C00013Q0004393Q001C000100201600013Q00040006140001001200013Q0004393Q001200010020AC00013Q0004001241000300053Q00202Q00030003000600202Q0003000300074Q0001000300014Q000100013Q00122Q000200086Q00010002000100201600013Q00090006140001001700013Q0004393Q001700010020AC00013Q00092Q008400010002000100201600013Q000A0006140001001C00013Q0004393Q001C00010020AC00013Q000A2Q00840001000200012Q00013Q00017Q000F3Q00030D3Q00506C6174666F726D5374616E6401002Q033Q0053697403093Q0057616C6B53702Q6564028Q0003093Q004A756D70506F77657203053Q007063612Q6C03083Q00416E63686F726564030E3Q0046696E6446697273744368696C6403063Q0053746174757303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q00422Q6F6C56616C756503043Q004E616D6500424Q009C7Q0006143Q001900013Q0004393Q001900012Q009C7Q0030613Q000100029Q0000304Q000300029Q0000206Q000400264Q000E000100050004393Q000E00012Q009C8Q009C000100013Q0010AD3Q000400012Q009C7Q0020165Q00060026043Q0015000100050004393Q001500012Q009C8Q009C000100023Q0010AD3Q000600010012A53Q00073Q00069900013Q000100012Q009C8Q00843Q000200012Q009C3Q00033Q0006143Q002200013Q0004393Q002200012Q009C3Q00033Q0020165Q00080006143Q002200013Q0004393Q002200012Q009C3Q00033Q0030593Q000800022Q009C3Q00044Q00773Q000100020006870001002900013Q0004393Q002900010020AC00013Q00090012320003000A4Q006D0001000300020006140001004100013Q0004393Q004100010012A50002000B3Q0020AC00030001000C2Q0019000300044Q006400023Q00040004393Q003F00010020AC00070006000D0012320009000E4Q006D0007000900020006140007003E00013Q0004393Q003E00012Q009C000700053Q00201600080006000F2Q00930007000200020006140007003E00013Q0004393Q003E00010012A5000700073Q00069900080001000100012Q00793Q00064Q00840007000200012Q002E00055Q00060A00020030000100020004393Q003000012Q00013Q00013Q00023Q00043Q00030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503073Q0052752Q6E696E6700074Q009A7Q00206Q000100122Q000200023Q00202Q00020002000300202Q0002000200046Q000200016Q00017Q00013Q0003073Q0044657374726F7900044Q009C7Q0020AC5Q00012Q00843Q000200012Q00013Q00017Q00023Q0003043Q007461736B03053Q00737061776E00104Q009C7Q0006143Q000400013Q0004393Q000400012Q00013Q00013Q0012A53Q00013Q0020165Q000200069900013Q000100062Q009C3Q00014Q009C3Q00024Q009C3Q00034Q009C3Q00044Q009C3Q00054Q009C8Q00933Q000200022Q008C8Q00013Q00013Q00013Q000C3Q0003083Q004175746F53652Q6C03043Q007461736B03043Q0077616974026Q00E03F03043Q007469636B030C3Q0053652Q6C496E74657276616C03203Q004175746F2053652Q6C3A20547279696E67206E6F2D74656C65706F72743Q2E030A3Q006E6F54656C65706F72742Q01026Q00F03F033C3Q004175746F2053652Q6C3A204E6F2D74656C65706F7274206661696C65642C2066612Q6C6261636B20746F20666F7263652074656C65706F72743Q2E030D3Q00666F72636554656C65706F727400374Q009C7Q0020165Q00010006143Q003400013Q0004393Q003400010012A53Q00023Q00201B5Q000300122Q000100048Q000200019Q0000206Q000100064Q000D000100010004393Q000D00010004393Q003400012Q009C3Q00013Q0006A95Q000100010004395Q00010012A53Q00054Q00093Q000100024Q000100029Q0000014Q00015Q00202Q00010001000600062Q00013Q00013Q0004395Q00012Q009C3Q00033Q00120B000100078Q000200016Q00046Q00013Q000100302Q0001000800096Q0002000200066Q000100010004395Q00012Q009C00015Q00201600010001000100061400013Q00013Q0004395Q00010012A5000100023Q00200800010001000300122Q0002000A6Q0001000200014Q000100013Q00062Q00013Q000100010004395Q00012Q009C000100033Q0012460002000B6Q0001000200014Q000100046Q00023Q000100302Q0002000C00094Q00010002000100046Q00012Q00A18Q008C3Q00054Q00013Q00017Q00023Q0003083Q004175746F53652Q6C012Q00034Q009C7Q0030593Q000100022Q00013Q00017Q000C3Q0003083Q004175746F53652Q6C0100028Q0003053Q00706169727303023Q005F4703053Q00466F72676503103Q00506C617965725549456C656D656E7473030E3Q004175746F53652Q6C546F2Q676C6503053Q007063612Q6C03123Q0053652Q6C496E74657276616C536C6964657203133Q00536B69704661766F7269746573546F2Q676C6503183Q00436F6E66696720726573657420746F2064656661756C747300304Q005C7Q00304Q000100029Q006Q00019Q008Q00023Q00124Q00038Q00033Q00124Q00046Q000100048Q0002000200044Q000E00012Q009C00056Q004D00050003000400060A3Q000C000100020004393Q000C00010012A53Q00053Q0020165Q00060020165Q00070006143Q002C00013Q0004393Q002C000100201600013Q00080006140001001C00013Q0004393Q001C00010012A5000100093Q00069900023Q000100012Q00798Q008400010002000100201600013Q000A0006140001002400013Q0004393Q002400010012A5000100093Q00069900020001000100022Q00798Q009C3Q00044Q008400010002000100201600013Q000B0006140001002C00013Q0004393Q002C00010012A5000100093Q00069900020002000100022Q00798Q009C3Q00044Q00840001000200012Q009C000100053Q0012320002000C4Q00840001000200012Q00013Q00013Q00033Q00023Q00030E3Q004175746F53652Q6C546F2Q676C652Q033Q0053657400064Q00557Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q0003123Q0053652Q6C496E74657276616C536C696465722Q033Q00536574030C3Q0053652Q6C496E74657276616C00074Q003F7Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003133Q00536B69704661766F7269746573546F2Q676C652Q033Q00536574030D3Q00536B69704661766F726974657300074Q003F7Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00023Q00030A3Q006E6F54656C65706F72742Q0100064Q00269Q0000013Q000100302Q0001000100026Q00019Q008Q00017Q00023Q00030D3Q00666F72636554656C65706F72742Q0100064Q00269Q0000013Q000100302Q0001000100026Q00019Q008Q00017Q00013Q0003103Q00436C65616E757020636F6D706C65746500084Q005E9Q003Q000100016Q00018Q000100016Q00023Q00122Q000100018Q000200016Q00017Q00", GetFEnv(), ...);
